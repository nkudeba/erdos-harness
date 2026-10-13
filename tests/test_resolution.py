"""resolution.py, the autonomous resolution campaign (2026-10-08): its queue, how it reads a finished engine pass, the
order of its tiers, its daily cap, and the Lean run it builds. No model calls and no subprocesses: everything that would
run is patched."""
import json, sys, tempfile, unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import resolution as R


def _claim(sess, cid, status, sig=None, settles=None, statement="s"):
    v = {"status": status}
    if sig is not None:
        v["novelty"] = {"verdict": "new", "significance": sig}
    if settles is not None:
        v["settles"] = settles
    return {"session": sess, "id": cid, "status": "PROVED", "statement": statement, "proof": "p", "validation": v}


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        d = Path(self.tmp.name)
        for name, val in (("CAMP", d), ("STATE", d / "state.json"), ("RESULTS", d / "results.jsonl"),
                          ("CONFIG", d / "config.json"), ("LOG", d / "log"), ("REVIEW", d / "REVIEW-NEEDED.md"),
                          ("SCREEN_RESULTS", d / "screen-results.jsonl"), ("PRESCREEN", d / "prescreen.jsonl")):
            p = patch.object(R, name, val)
            p.start()
            self.addCleanup(p.stop)
        self.d = d

    def engine_run(self, ledger) -> Path:
        self.k = getattr(self, "k", 0) + 1
        run = self.d / "runs" / f"20261008-000000-00000{self.k}-erdos99"
        (run / "engine").mkdir(parents=True)
        (run / "engine" / "engine.json").write_text(json.dumps({"ledger": ledger}))
        (run / "state.json").write_text(json.dumps({"statement": "theorem erdos_99 : True := by\n  sorry",
                                                    "statement_source": "formal-conjectures"}))
        (run / "problem.json").write_text(json.dumps({"id": "99", "statement": "Is it true?"}))
        return run


class Classify(Base):
    def test_complete_needs_both_settles_judges(self):
        both = {"settles": True, "answer": "false", "judges": [{"settles": True}, {"settles": True}]}
        run = self.engine_run([_claim("deep", "C1", "validated-new", 3, settles=both, statement="the answer is no")])
        out, info = R.classify(run)
        self.assertEqual((out, info["claim"], info["answer"]), ("complete", "deep/C1", "false"))

    def test_traction_and_none(self):
        run = self.engine_run([_claim("r1s1", "C1", "validated-new", 2), _claim("r1s2", "C1", "validated-new", 1)])
        out, info = R.classify(run)
        self.assertEqual(out, "traction")
        self.assertEqual([c["claim"] for c in info["claims"]], ["r1s1/C1"])
        run2 = self.engine_run([_claim("r1s1", "C1", "validated-new", 1), _claim("r1s2", "C1", "broken")])
        self.assertEqual(R.classify(run2)[0], "none")


class Ripeness(Base):
    def test_a_deep_pass_needs_a_plausible_settle_or_a_significance_3_claim(self):
        def run(chance, sig):
            r = self.engine_run([_claim("r1s1", "C1", "validated-new", sig)])
            ej = json.loads((r / "engine" / "engine.json").read_text())
            ej["deep"] = {"settle_chance": chance}
            (r / "engine" / "engine.json").write_text(json.dumps(ej))
            return R.classify(r)[0]
        self.assertEqual(run(0.0, 2), "not ripe")        # #366: its own team lead saw no settling line
        self.assertEqual(run(0.3, 2), "traction")
        self.assertEqual(run(0.0, 3), "traction")        # a claim already rated 3 earns the deep pass anyway
        self.assertEqual(run(None, 2), "traction")       # a run from before the field


class Tiers(Base):
    def test_lean_then_deep_then_a_cut_off_stage_then_the_queue(self):
        cfg = R.load_cfg()
        st = {"problems": {"5": {"next": "deep"}, "6": {"next": "lean"}, "7": {"running": "scout"}}}
        with patch.object(R, "queue", lambda s, c: [8, 9]):
            self.assertEqual(R.next_action(st, cfg), ("lean", 6))
            st["problems"]["6"]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("deep", 5))
            st["problems"]["5"]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("scout", 7))
            st["problems"]["7"]["running"] = None
            self.assertEqual(R.next_action(st, cfg), ("screen", 8))                         # a new problem: its screen
            st["problems"]["7"].update({"running": "scout", "errors": cfg["max_errors"]})   # gave up on it
            self.assertEqual(R.next_action(st, cfg), ("screen", 8))

    def test_the_daily_cap_counts_the_last_24_hours(self):
        now = datetime(2026, 10, 8, 12, tzinfo=timezone.utc)
        for hours, spend in ((1, 10.0), (23, 5.0), (25, 100.0)):
            at = (now - timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
            with R.RESULTS.open("a") as f:
                f.write(json.dumps({"at": at, "spend": spend}) + "\n")
        self.assertEqual(R.spent_since(24, now), 15.0)
        self.assertEqual(R.spent_since(168, now), 115.0)
        # a prescreen sweep beside the loop counts too
        R.PRESCREEN.write_text(json.dumps({"problem": "1", "mean": 0.1, "cost": 0.4,
                                           "at": (now - timedelta(hours=2)).strftime("%Y-%m-%dT%H:%M:%SZ")}) + "\n")
        self.assertAlmostEqual(R.spent_since(24, now), 15.4)


class Screen(Base):
    """2026-10-08, REPORT 3.8: a cheap SETTLE CHANCE from the map alone decides which problems are scouted. A problem below
    the bar is still scouted in the control arm, a fixed quarter chosen by its number, so the arms measure the screen."""

    def _screened(self, mean, draws=None):
        run = self.engine_run([])
        ej = json.loads((run / "engine" / "engine.json").read_text())
        ej["settle_screen"] = {"mean": mean, "draws": [{"chance": c, "goal": "SETTLE CHANCE: 0.4\nProve the core by a sieve."}
                                                       for c in (draws if draws is not None else [mean])]}
        (run / "engine" / "engine.json").write_text(json.dumps(ej))
        return run

    def test_the_arms(self):
        cfg = R.load_cfg()
        self.assertEqual(R.arm(5, 0.3, cfg), "pass")
        lows = [R.arm(n, 0.05, cfg) for n in range(1, 1218)]
        self.assertEqual(set(lows), {"control", "screened out"})
        self.assertTrue(0.2 < lows.count("control") / len(lows) < 0.3)
        # by the number, never by the chance
        self.assertEqual([R.arm(n, 0.0, cfg) for n in range(1, 60)], [R.arm(n, 0.29, cfg) for n in range(1, 60)])

    def test_a_screen_sends_a_problem_to_its_scout_or_screens_it_out(self):
        cfg = R.load_cfg()
        control = next(n for n in range(1, 999) if R.arm(n, 0.0, cfg) == "control")
        out = next(n for n in range(1, 999) if R.arm(n, 0.0, cfg) == "screened out")
        with patch.object(R, "record_atlas") as atlas, patch.object(R, "commit"):
            for n, mean, want in ((11, 0.45, "pass"), (out, 0.05, "screened out"), (control, 0.05, "control")):
                state = {"problems": {str(n): {"history": [], "run_dir": "runs/x", "spend": 3.2}}}
                p = state["problems"][str(n)]
                R.finish_screen(n, p, cfg, self._screened(mean), 3.2)
                self.assertEqual((p["arm"], p["next"]), (want, None if want == "screened out" else "scout"))
            self.assertIn("SETTLE CHANCE 0.45", atlas.call_args_list[0][0][1])
            self.assertIn("Prove the core by a sieve", atlas.call_args_list[0][0][1])
        self.assertEqual([(r["tier"], r["outcome"]) for r in R.rows()],
                         [("screen", "pass"), ("screen", "screened out"), ("screen", "control")])

    def test_a_screen_with_no_number_is_tried_again_then_given_up(self):
        cfg = R.load_cfg()
        state = {"problems": {"12": {"history": [], "run_dir": "runs/x"}}}
        p = state["problems"]["12"]
        with patch.object(R, "record_atlas") as atlas, patch.object(R, "commit"):
            R.finish_screen(12, p, cfg, self._screened(None, [None, None]), 3.0)
            self.assertEqual((p["running"], p["errors"]), ("screen", 1))
            R.finish_screen(12, p, cfg, self._screened(None, [None, None]), 0.5)
            self.assertEqual((p["running"], p["status"]), (None, "screen failed"))
            atlas.assert_not_called()

    def test_scouts_take_the_pass_arm_first_highest_chance_first_then_the_control_arm(self):
        cfg = R.load_cfg()
        st = {"problems": {"1": {"next": "scout", "arm": "control", "settle_chance": 0.05},
                           "2": {"next": "scout", "arm": "pass", "settle_chance": 0.4},
                           "3": {"next": "scout", "arm": "pass", "settle_chance": 0.6}}}
        with patch.object(R, "queue", lambda s, c: [8]):
            for want in (3, 2, 1):
                self.assertEqual(R.next_action(st, cfg), ("scout", want))
                st["problems"][str(want)]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("screen", 8))

    def test_a_scout_resumes_the_screen_run_and_its_budget_counts_the_screen(self):
        cfg, seen = R.load_cfg(), {}

        def fake(n, tag, total, flags, resume=None, on_start=None):
            seen.update(tag=tag, total=total, flags=flags, resume=resume)
            return None, 1
        R.save_state({"problems": {"7": {"history": [], "next": "scout", "arm": "pass", "settle_chance": 0.5,
                                         "prepped": True, "run_dir": "runs/r7", "spend": 4.0}}})
        with patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: []):
            R.step(cfg)
        self.assertEqual((seen["tag"], seen["total"], seen["resume"]), ("resolve-scout", 22.0, "runs/r7"))
        self.assertIn("--engine-settle-draws 2", seen["flags"])    # a backfilled pass gets the screen on its own map
        R.save_state({"problems": {}})
        with patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: [9]), \
                patch.object(R, "prep", lambda n, c: {"ok": True}), patch.object(R, "adopt_run", lambda n: None):
            R.step(cfg)
        self.assertEqual((seen["tag"], seen["total"], seen["resume"]), ("resolve-screen", 12.0, None))
        for flag in ("--engine-sessions 0", "--engine-settle-draws 2", "--engine-deep-budget 0", "--engine-objective resolve"):
            self.assertIn(flag, seen["flags"])


class UsageLimit(Base):
    """2026-10-09 to 10-13: the weekly limit made every screen fail twice, and the campaign gave up ten problems it
    never screened. A stage that ends on a usage limit now waits for the stated reset and resumes, with no error."""

    def test_a_limit_is_an_outage_not_an_error(self):
        cfg, run = R.load_cfg(), self.d / "runs" / "20261011-174757-518493-erdos197"
        run.mkdir(parents=True)
        (run / "lane.log").write_text("...\nRuntimeError: claude -p returned an error result (engine-frontier): success: "
                                      "You've hit your weekly limit · resets Oct 13 at 9am (America/Toronto)\n")
        R.save_state({"problems": {"197": {"history": [], "running": "screen", "prepped": True, "run_dir": str(run)}}})
        slept = []
        with patch.object(R, "run_screen", lambda *a, **k: (None, 0)), patch.object(R, "queue", lambda s, c: []), \
                patch.object(R.time, "sleep", slept.append):
            R.step(cfg)
        p = R.load_state()["problems"]["197"]
        self.assertEqual((p.get("errors"), p["running"], p["limit_waits"]), (None, "screen", 1))
        self.assertTrue(slept and slept[0] > 60)
        self.assertEqual(R.rows()[-1]["outcome"], "usage limit")
        # a failure that is not a limit still counts
        (run / "lane.log").write_text("Traceback ...\nValueError: something else broke\n")
        with patch.object(R, "run_screen", lambda *a, **k: (None, 0)), patch.object(R, "queue", lambda s, c: []):
            R.step(cfg)
        self.assertEqual(R.load_state()["problems"]["197"]["errors"], 1)


class Backfill(Base):
    """REPORT 3.9: screens drawn from maps already on disk. A pass enters the pass arm; nothing is screened out on them."""

    def test_only_a_pass_comes_in_and_each_row_is_logged_once(self):
        cfg = R.load_cfg()
        f = self.d / "open.jsonl"
        f.write_text("\n".join(json.dumps(r) for r in (
            {"problem": 20, "run_dir": "runs/a", "mean": 0.4, "draws": [0.4, 0.4], "cost": 0.6},
            {"problem": 64, "run_dir": "runs/b", "mean": 0.05, "draws": [0.1, 0.0], "cost": 0.5},
            {"problem": 99, "run_dir": "runs/c", "mean": 0.9, "draws": [0.9, 0.9], "cost": 0.5})) + "\n")
        R.save_state({"problems": {"7": {"history": [], "status": "done"}}})
        with patch.object(R, "queue", lambda s, c: [20, 64]):           # #99 is not a campaign target
            self.assertEqual(R.import_screens(f, cfg), [20])
            self.assertEqual(R.import_screens(f, cfg), [])                # a second import adds nothing
        st = R.load_state()["problems"]
        self.assertEqual((st["20"]["arm"], st["20"]["next"]), ("pass", "scout"))
        self.assertNotIn("64", st)                                        # keeps its place in the queue
        self.assertIn("7", st)                                            # other entries survive
        self.assertAlmostEqual(R.spent_since(), 1.6)

    def test_a_stage_writes_only_its_own_problem(self):
        R.save_state({"problems": {"1": {"history": []}}})
        p = R.load_state()["problems"]["1"]
        R.save_problem(2, {"history": [], "status": "imported meanwhile"})
        p["status"] = "done"
        R.save_problem(1, p)
        self.assertEqual({k: v.get("status") for k, v in R.load_state()["problems"].items()},
                         {"1": "done", "2": "imported meanwhile"})


class Restarts(Base):
    """2026-10-08: a Ctrl-C mid-scout and a restart began #366 afresh, abandoning $9.85 of work, and a second terminal ran
    a second loop that would have raced the first."""

    def test_an_interrupted_scout_is_adopted_by_its_work(self):
        root = self.d / "root"
        for name, spend in (("20261008-112020-000001-erdos366", 9.85), ("20261008-130320-000002-erdos366", 1.2),
                            ("20261008-140000-000003-erdos366", None)):
            r = root / "runs" / name
            (r / "engine").mkdir(parents=True)
            (r / "problem.json").write_text(json.dumps({"id": "366", "notes": "OPEN problem. Research engine screen resolve-scout (no Lean)."}))
            if spend is not None:
                (r / "engine" / "checkpoint.json").write_text(json.dumps({"spend": spend}))
        other = root / "runs" / "20261008-150000-000004-erdos366"          # not a campaign run
        (other / "engine").mkdir(parents=True)
        (other / "problem.json").write_text(json.dumps({"id": "366", "notes": "Research engine screen s6-probe"}))
        (other / "engine" / "checkpoint.json").write_text(json.dumps({"spend": 50.0}))
        with patch.object(R, "ROOT", root):
            self.assertEqual(R.adopt_run(366), "runs/20261008-112020-000001-erdos366")
            self.assertIsNone(R.adopt_run(999))

    def test_a_second_loop_exits(self):
        first = R.single_instance()
        self.assertIsNotNone(first)
        self.assertIsNone(R.single_instance())
        first.close()
        again = R.single_instance()
        self.assertIsNotNone(again)
        again.close()


class ClaimLean(Base):
    """2026-10-08, the operator: "Wherever possible do a Lean check." A validated-new claim at significance 2 or more
    gets a Lean run of its own after the problem's main tiers."""

    def test_which_claims_and_how_the_run_is_built(self):
        run = self.engine_run([_claim("r1s1", "C1", "validated-new", 2, statement="the k = 3 case holds"),
                               _claim("r1s2", "C1", "validated-new", 1), _claim("deep", "C1", "validated-new", 3),
                               _claim("r1s3", "C1", "broken", 3)])
        self.assertEqual(R.claims_for_lean(run, 2, set()), ["deep/C1", "r1s1/C1"])
        self.assertEqual(R.claims_for_lean(run, 2, {"deep/C1"}), ["r1s1/C1"])
        with patch.object(R, "ROOT", self.d):
            lean = R.build_claim_lean_run(99, run, "r1s1/C1", 1)
            cmd = R.claim_lean_cmd(lean, R.load_cfg())
        prob = json.loads((lean / "problem.json").read_text())
        st = json.loads((lean / "state.json").read_text())
        self.assertEqual((prob["id"], prob["statement"]), ("10009901", "the k = 3 case holds"))
        self.assertNotIn("statement", st)                     # the harness formalizes the claim itself
        self.assertEqual((st["partial_of"], st["claim"]), (99, "r1s1/C1"))
        self.assertIn("the k = 3 case holds", st["discovery"]["best_proof"]["text"])
        self.assertNotIn("--open", cmd)
        self.assertNotIn("--benchmark", cmd)

    def test_the_claim_tier_comes_after_the_problem_tiers(self):
        cfg = R.load_cfg()
        st = {"problems": {"5": {"claims_todo": ["r1s1/C1"]}, "6": {"next": "deep"}}}
        with patch.object(R, "queue", lambda s, c: [8]):
            self.assertEqual(R.next_action(st, cfg), ("deep", 6))
            st["problems"]["6"]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("lean-claim", 5))
            st["problems"]["5"]["claims_todo"] = []
            self.assertEqual(R.next_action(st, cfg), ("screen", 8))


class Queue(Base):
    def test_priority_first_then_least_studied_and_never_a_claimed_or_taken_problem(self):
        ranks = {"problems": [{"id": n, "status": "Unsolved", "partial": {"score": 50}} for n in (1, 2, 3, 4, 5)]
                 + [{"id": 6, "status": "Solved"}]}
        chars = {1: 900, 2: 100, 3: 500, 4: 50, 5: 10}
        fake_root = self.d / "root"
        (fake_root / "atlas-data").mkdir(parents=True)
        (fake_root / "atlas-data" / "rankings.json").write_text(json.dumps(ranks))
        (fake_root / "atlas-data" / "openai-math-2026-10-06.json").write_text(json.dumps(
            {"claimed_resolved": [{"problem": "5", "family": "1"}], "claimed_partial": []}))
        with patch.object(R, "ROOT", fake_root), patch.object(R, "forum_chars", lambda n: chars[n]):
            q = R.queue({"problems": {"2": {}}}, {"priority": [3]})
        self.assertEqual(q, [3, 4, 1])          # 3 by priority; 5 claimed, 2 taken, 6 solved; then least studied
        # a prescreen's chance, where one exists, orders the rest first (REPORT 3.10)
        R.PRESCREEN.write_text(json.dumps({"problem": "1", "mean": 0.4}) + "\n" + json.dumps({"problem": "4", "mean": None}) + "\n")
        with patch.object(R, "ROOT", fake_root), patch.object(R, "forum_chars", lambda n: chars[n]):
            self.assertEqual(R.queue({"problems": {"2": {}}}, {"priority": [3]}), [3, 1, 4])


class Lean(Base):
    def test_the_lean_run_is_a_normal_open_problem_run_committed_to_the_chains_direction(self):
        both = {"settles": True, "answer": "false", "judges": [{"settles": True}, {"settles": True}]}
        run = self.engine_run([_claim("deep", "C1", "validated-new", 3, settles=both, statement="no such set exists")])
        with patch.object(R, "ROOT", self.d):
            lean = R.build_lean_run(99, run, "deep/C1", "false")
            cmd = R.lean_cmd(lean, R.load_cfg())
        st = json.loads((lean / "state.json").read_text())
        self.assertEqual(st["discovery"]["decision"]["commit"], "neg")
        self.assertIn("no such set exists", st["discovery"]["best_proof"]["text"])
        self.assertNotIn("benchmark", st)                       # a verified proof belongs in knowledge/ and the Atlas
        self.assertIn("none: the informal proof is the harness's own", st["assistance"][0])
        self.assertIn("--open", cmd)
        self.assertNotIn("--benchmark", cmd)
        self.assertEqual(cmd[cmd.index("--discover") + 1], "on")      # open mode reads the seeded decision

    def test_a_verified_result_is_flagged_for_review(self):
        run = self.engine_run([])
        with patch.object(R, "ROOT", self.d):
            R.flag_for_review(99, run, "RUN-SUMMARY problem=99 exit=0", "deep/C1", run)
        text = R.REVIEW.read_text()
        self.assertIn("independent human review", text)
        self.assertIn("## #99", text)


if __name__ == "__main__":
    unittest.main()
