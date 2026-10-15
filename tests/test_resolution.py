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
                          ("SCREEN_RESULTS", d / "screen-results.jsonl"), ("PRESCREEN", d / "prescreen.jsonl"),
                          ("FINDINGS", d / "STATEMENT-FINDINGS.md")):
            p = patch.object(R, name, val)
            p.start()
            self.addCleanup(p.stop)
        for name, val in (("site_claims", lambda n: 0),          # the real forum cache must not decide a test
                          ("refresh_forum", lambda n: None),       # no network in a test
                          ("refresh_sources", lambda cfg, every_hours=6.0: False),
                          ("FRESH", d / "fresh"), ("SURVEY", d / "survey.json")):
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
                patch.object(R, "prep", lambda n, c: {"ok": True}), patch.object(R, "adopt_run", lambda n, **k: None):
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


class Tracks(Base):
    """2026-10-13: a pass goes to the new-mathematics track unless its intent judges call the line a formalization gap or
    a known result; new mathematics gets the research program; a verified statement finding is reported as one."""

    def _finish_scout(self, n, track, ledger, deep_chance=None):
        run = self.engine_run(ledger)
        ej = json.loads((run / "engine" / "engine.json").read_text())
        ej["deep"] = {"settle_chance": deep_chance}
        (run / "engine" / "engine.json").write_text(json.dumps(ej))
        R.save_state({"problems": {str(n): {"history": [], "next": "scout", "arm": "pass" if track != "control" else "control",
                                            "prepped": True, "run_dir": str(run), "spend": 3.0,
                                            **({"track": track} if track else {})}}})
        with patch.object(R, "run_screen", lambda *a, **k: ({"run_dir": str(run), "spend_run": 21.0}, 0)), \
                patch.object(R, "queue", lambda s, c: []), patch.object(R, "record_atlas"), patch.object(R, "commit"):
            R.step(R.load_cfg())
        return R.load_state()["problems"][str(n)]

    def test_the_intent_decides_the_track(self):
        self.assertEqual(R.track_for("pass", "new-math"), "new-math")
        self.assertEqual(R.track_for("pass", None), "new-math")              # unclassified: keep the candidate
        self.assertEqual(R.track_for("pass", "formalization-gap"), "statement")
        self.assertEqual(R.track_for("pass", "known-result"), "statement")
        self.assertEqual(R.track_for("control", "known-result"), "control")
        self.assertIsNone(R.track_for("screened out", "new-math"))
        run = self.engine_run([])
        ej = json.loads((run / "engine" / "engine.json").read_text())
        ej.update({"settle_screen": {"mean": 0.85, "draws": [{"chance": 0.85, "goal": "the regular n-gon"}]},
                   "intent": {"class": "formalization-gap"}})
        (run / "engine" / "engine.json").write_text(json.dumps(ej))
        state = {"problems": {"655": {"history": [], "run_dir": "runs/x"}}}
        p = state["problems"]["655"]
        with patch.object(R, "record_atlas"), patch.object(R, "commit"):
            R.finish_screen(655, p, R.load_cfg(), run, 3.0)
        self.assertEqual((p["arm"], p["track"], p["intent"]), ("pass", "statement", "formalization-gap"))

    def test_new_mathematics_gets_the_research_program(self):
        p = self._finish_scout(11, "new-math", [_claim("r1s1", "C1", "validated-new", 1)])
        self.assertEqual((p["next"], p["status"]), ("program", "program"))
        p = self._finish_scout(12, "new-math", [], deep_chance=0.02)      # its own team lead saw no route
        self.assertIsNone(p["next"])
        p = self._finish_scout(13, "statement", [_claim("r1s1", "C1", "validated-new", 2)])
        self.assertIsNone(p["next"])                                        # a statement finding gets no deep pass
        p = self._finish_scout(14, "control", [_claim("r1s1", "C1", "validated-new", 2)])
        self.assertEqual(p["next"], "deep")                                 # the control arm keeps its protocol
        p = self._finish_scout(15, None, [_claim("r1s1", "C1", "validated-new", 1)])
        self.assertEqual((p["track"], p["next"]), ("new-math", "program"))  # a pass screened before tracks

    def test_the_program_stage_resumes_the_scout_run(self):
        seen = {}

        def fake(n, tag, total, flags, resume=None, on_start=None):
            seen.update(tag=tag, total=total, flags=flags, resume=resume)
            return None, 1
        R.save_state({"problems": {"7": {"history": [], "next": "program", "track": "new-math", "run_dir": "runs/r7",
                                         "spend": 21.0}}})
        with patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: []):
            R.step(R.load_cfg())
        self.assertEqual((seen["tag"], seen["total"], seen["resume"]), ("resolve-program", 111.0, "runs/r7"))
        self.assertIn("--engine-program-cycles 6", seen["flags"])

    def test_a_verified_statement_finding_is_reported_as_one(self):
        run, lean = self.engine_run([]), self.d / "runs" / "lean"
        lean.mkdir(parents=True)
        (lean / "SUMMARY.line").write_text("RUN-SUMMARY problem=655 exit=0 spend=$4.00")
        complete = {"claim": "program/C3", "answer": "false", "statement": "the regular n-gon", "intent": "formalization-gap"}
        R.save_state({"problems": {"655": {"history": [], "next": "lean", "track": "statement", "run_dir": str(run),
                                           "lean_run": str(lean), "complete": complete}}})
        with patch.object(R, "ROOT", self.d), patch.object(R, "run_lean", lambda *a, **k: (0, "RUN-SUMMARY exit=0")), \
                patch.object(R, "record_atlas") as atlas, patch.object(R, "commit"), patch.object(R, "queue", lambda s, c: []):
            R.step(R.load_cfg())
        self.assertIn("## #655 — formalization-gap", R.FINDINGS.read_text())
        self.assertFalse(R.REVIEW.exists())
        self.assertIn("not a resolution of the problem as posed", atlas.call_args[0][1])


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
        self.assertEqual(cmd[cmd.index("--child-cycles") + 1], "3")        # REPORT 3.11: children were starved at 1
        self.assertEqual(cmd[cmd.index("--residual-depth") + 1], "3")

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


class ClaimedProblems(Base):
    """The operator's rule (2026-10-15): a problem with proof claims on erdosproblems.com is skipped."""

    def test_the_claims_count_comes_from_the_cached_claims_page(self):
        with tempfile.TemporaryDirectory() as tmp:
            forum = Path(tmp) / "atlas-data" / "forum"
            forum.mkdir(parents=True)
            (forum / "9.json").write_text(json.dumps({"claims": "Menu\n There are 3 proof claims (partial or full)"}))
            (forum / "10.json").write_text(json.dumps({"claims": "There is 1 proof claim (partial or full)"}))
            (forum / "11.json").write_text(json.dumps({"claims": "No proof claims yet."}))
            with patch.object(R, "ROOT", Path(tmp)):
                # Base stubs R.site_claims; the real function is the one captured at import
                self.assertEqual([ORIGINAL_SITE_CLAIMS(n) for n in (9, 10, 11, 12)], [3, 1, 0, 0])

    def test_the_queue_leaves_claimed_problems_out(self):
        with patch.object(R, "site_claims", lambda n: 2 if n == 8 else 0), patch.object(R, "prescreen", lambda: {}), \
                patch.object(R, "forum_chars", lambda n: n):
            fake = self.d / "rk"
            (fake / "atlas-data").mkdir(parents=True)
            (fake / "atlas-data" / "rankings.json").write_text(json.dumps({"problems": [
                {"id": i, "status": "Unsolved"} for i in (7, 8, 9)]}))
            with patch.object(R, "ROOT", fake):
                self.assertEqual(R.queue({"problems": {}}, {"priority": [8]}), [7, 9])

    def test_a_screen_whose_fresh_forum_shows_claims_is_skipped_at_no_cost(self):
        R.save_state({"problems": {}})
        ran = []
        with patch.object(R, "queue", lambda s, c: [8]), patch.object(R, "prep", lambda n, c: {"ok": True}), \
                patch.object(R, "site_claims", lambda n: 3), patch.object(R, "run_screen", lambda *a, **k: ran.append(a)):
            R.step(R.load_cfg())
        p = R.load_state()["problems"]["8"]
        self.assertEqual((p["status"], p["next"], p["running"]), ("skipped", None, None))
        self.assertIn("3 proof claim(s)", p["why"])
        self.assertFalse(ran)

    def test_a_claimed_problem_gets_no_deep_or_program_pass(self):
        # #1110: a loop older than the rule finished its scout and would have routed it to a $40 deep pass
        for tier in ("deep", "program"):
            R.save_state({"problems": {"1110": {"history": [], "next": tier, "run_dir": "runs/r"}}})
            ran = []
            with patch.object(R, "site_claims", lambda n: 3), patch.object(R, "run_screen", lambda *a, **k: ran.append(a)):
                R.step(R.load_cfg())
            p = R.load_state()["problems"]["1110"]
            self.assertEqual((p["status"], p["next"], ran), ("skipped", None, []), tier)


class LanesAndFreshness(Base):
    """2026-10-15: record and explicit tracks beside settle, and freshly formalized problems first."""

    def setUp(self):
        super().setUp()
        (self.d / "atlas-data").mkdir()
        (self.d / "atlas-data" / "rankings.json").write_text(json.dumps({"problems": [
            {"id": i, "status": "Unsolved"} for i in range(1, 30)]}))
        (self.d / "fresh").mkdir()
        (self.d / "fresh" / "problems-2026-10-15.yaml").write_text(
            "- number: '5'\n  status: {state: open}\n  formalized: {state: 'yes', last_update: '2026-10-13'}\n"
            "- number: '6'\n  status: {state: open}\n  formalized: {state: 'yes', last_update: '2026-10-01'}\n"
            "- number: '7'\n  status: {state: proved}\n  formalized: {state: 'yes', last_update: '2026-10-14'}\n"
            "- number: '8'\n  status: {state: open}\n  formalized: {state: 'yes', last_update: '2025-01-01'}\n")
        (self.d / "survey.json").write_text(json.dumps({
            "records": [{"problem": 11, "score": 4.0, "claims": 0}, {"problem": 12, "score": 3.0, "claims": 2},
                        {"problem": 13, "score": 2.5, "claims": 0}],
            "explicit": [{"problem": 21, "score": 2.0, "claims": 0}, {"problem": 5, "score": 1.0, "claims": 0}]}))

    def queue(self, **cfg):
        today = R.datetime(2026, 10, 15, tzinfo=R.timezone.utc)
        with patch.object(R, "ROOT", self.d), patch.object(R, "prescreen", lambda: {}), patch.object(R, "forum_chars", lambda n: n), \
                patch.object(R, "fresh_targets", lambda c: ORIGINAL_FRESH_TARGETS(c, now=today)), \
                patch.object(R, "site_claims", lambda n: 2 if n == 12 else 0):      # as the survey says
            return R.queue({"problems": {"13": {}}}, {"priority": [], **cfg})

    def test_fresh_formalizations_lead_and_the_lanes_interleave(self):
        q = self.queue()
        # fresh newest first (#5, then #6 within 30 days; proved #7 and stale #8 never), record (#12 claimed, #13
        # taken), explicit (#5 already placed), then the rest of the settle lane
        self.assertEqual(q[:5], [5, 11, 21, 1, 6])
        self.assertEqual((R.QUEUE_LANE[5], R.QUEUE_LANE[11], R.QUEUE_LANE[21], R.QUEUE_LANE[1]),
                         ("fresh", "record", "explicit", "settle"))
        self.assertNotIn(12, q)
        self.assertNotIn(13, q)

    def test_a_lane_weighted_zero_is_off(self):
        q = self.queue(mix={"fresh": 0, "record": 2, "explicit": 0, "settle": 1})
        self.assertEqual(q[:3], [11, 1, 2])                  # record twice per round, but it has only one target left
        self.assertEqual(R.QUEUE_LANE[21], "settle")         # off as a track, #21 is still an ordinary settle target

    def test_a_settle_screen_out_is_screened_again_once_by_a_computational_lane(self):
        state = {"problems": {"13": {}, "21": {"status": "screened out", "kind": "settle", "history": []}}}
        today = R.datetime(2026, 10, 15, tzinfo=R.timezone.utc)
        with patch.object(R, "ROOT", self.d), patch.object(R, "prescreen", lambda: {}), patch.object(R, "forum_chars", lambda n: n), \
                patch.object(R, "fresh_targets", lambda c: ORIGINAL_FRESH_TARGETS(c, now=today)):
            q = R.queue(state, {"priority": []})
            self.assertEqual(R.QUEUE_LANE[21], "explicit")
            state["problems"]["21"]["rescreened"] = True
            self.assertNotIn(21, R.queue(state, {"priority": []}))
        R.save_state({"problems": {"21": {"status": "screened out", "kind": "settle", "run_dir": "runs/old", "spend": 3.0,
                                          "settle_chance": 0.01, "prepped": True, "history": []}}})
        seen = {}
        R.QUEUE_LANE.clear()
        R.QUEUE_LANE[21] = "explicit"
        with patch.object(R, "queue", lambda s, c: [21]), patch.object(R, "adopt_run", lambda n, **k: None), \
                patch.object(R, "run_screen", lambda n, tag, total, flags, resume=None, on_start=None:
                             (seen.update(flags=flags, resume=resume) or (None, 1))):
            R.step(R.load_cfg())
        p = R.load_state()["problems"]["21"]
        self.assertEqual((p["kind"], p["previous"]["run_dir"], p["rescreened"]), ("explicit", "runs/old", True))
        self.assertIsNone(seen["resume"])                      # a new run, not the settle run resumed
        self.assertIn("--engine-objective explicit", seen["flags"])

    def test_a_rescreen_never_adopts_the_run_it_replaces(self):
        def run(name, spend):
            r = self.d / "runs" / name
            (r / "engine").mkdir(parents=True)
            (r / "problem.json").write_text(json.dumps({"notes": "Research engine screen resolve-screen (no Lean)."}))
            (r / "engine" / "checkpoint.json").write_text(json.dumps({"spend": spend}))
            return str(r.relative_to(self.d))
        old, new = run("20261010-090000-000000-erdos21", 5.0), run("20261015-170000-000000-erdos21", 1.0)
        with patch.object(R, "ROOT", self.d):
            self.assertEqual(R.adopt_run(21), old)                                  # the most work wins, as before
            self.assertEqual(R.adopt_run(21, exclude={old}), new)
            self.assertEqual(R.adopt_run(21, after="20261015-160000"), new)
            self.assertIsNone(R.adopt_run(21, exclude={old}, after="20261016-000000"))

    def test_the_objective_follows_the_kind(self):
        cfg = R.load_cfg()
        self.assertIn("--engine-objective resolve", R.stage_flags(cfg, "scout", {}))
        self.assertIn("--engine-objective record", R.stage_flags(cfg, "scout", {"kind": "record"}))
        self.assertIn("--engine-objective explicit", R.stage_flags(cfg, "deep", {"kind": "explicit"}))
        self.assertNotIn("resolve", R.stage_flags(cfg, "screen", {"kind": "record"}))

    def test_a_first_screen_takes_its_lanes_kind_and_runs_its_objective(self):
        R.save_state({"problems": {}})
        seen = {}

        def fake_screen(n, tag, total, flags, resume=None, on_start=None):
            seen["flags"] = flags
            return None, 1
        R.QUEUE_LANE.clear()
        R.QUEUE_LANE[11] = "record"
        with patch.object(R, "queue", lambda s, c: [11]), patch.object(R, "prep", lambda n, c: {"ok": True, "fc_sha": "head"}), \
                patch.object(R, "run_screen", fake_screen):
            R.step(R.load_cfg())
        p = R.load_state()["problems"]["11"]
        self.assertEqual((p["kind"], p["lane"], p["fc_sha"]), ("record", "record", "head"))
        self.assertIn("--engine-objective record", seen["flags"])

    def test_a_statement_newer_than_the_pinned_commit_is_frozen_at_the_head(self):
        import timesplit as T
        calls = []

        def fake_fetch(url, dest, refresh=False, pause=0.0, tries=4):
            calls.append(url)
            return "" if "/pinned/" in url else "theorem erdos_9 : True ↔ answer(True) := by\n  sorry\n"
        cfg = {**R.load_cfg(), "fc_sha": "pinned", "fc_head_sha": "head"}
        with patch.object(T, "fetch", fake_fetch), patch.object(R, "_thread_digest", lambda: (lambda n: "digest")), \
                patch.object(R, "ROOT", self.d):
            info = R.prep(9, cfg)
        self.assertEqual((info["ok"], info["fc_sha"]), (True, "head"))
        self.assertTrue(any("/head/" in u for u in calls))

    def test_a_computational_runs_claims_need_a_passing_certificate(self):
        def claim(cid, check, sig):
            c = _claim("r1s1", cid, "validated-new", sig, statement=f"record {cid}")
            if check:
                c["certificate_check"] = check
            return c
        run = self.engine_run([claim("C1", "CERTIFIED", 1), claim("C2", "FAILED", 2), claim("C3", None, 2)])
        self.assertEqual(R.claims_for_lean(run, 1, set(), certified=True), ["r1s1/C1"])
        self.assertEqual(sorted(R.claims_for_lean(run, 2, set())), ["r1s1/C2", "r1s1/C3"])

    def test_sources_refresh_at_most_every_few_hours(self):
        import timesplit as T
        R.refresh_sources = ORIGINAL_REFRESH_SOURCES                     # Base stubs it; test the real one here
        self.addCleanup(setattr, R, "refresh_sources", lambda cfg, every_hours=6.0: False)

        def fake_fetch(url, dest, refresh=False, pause=0.0, tries=4):
            Path(dest).parent.mkdir(parents=True, exist_ok=True)
            body = json.dumps({"sha": "abc123"}) if "commits" in url else "- number: '1'\n"
            Path(dest).write_text(body)
            return body
        (self.d / "survey.json").write_text("{}")
        with patch.object(T, "fetch", fake_fetch):
            self.assertTrue(R.refresh_sources(R.load_cfg()))
            self.assertFalse(R.refresh_sources(R.load_cfg()))           # within the window: nothing fetched
        self.assertEqual(json.loads(R.CONFIG.read_text())["fc_head_sha"], "abc123")
        self.assertTrue(list((self.d / "fresh").glob("problems-*.yaml")))


class Compute(Base):
    """The computation tier (2026-10-15): a record run's sessions ask for long computations, the campaign runs them in
    the sandbox with no model calls, and the next stage reads the output."""

    def session(self, run, label, notebook, scripts):
        sb = run / "engine" / "sessions" / label
        sb.mkdir(parents=True, exist_ok=True)
        (sb / "NOTEBOOK.md").write_text(notebook)
        for name, body in scripts.items():
            (sb / name).write_text(body)

    def test_requests_are_read_once_and_only_for_real_scripts(self):
        run = self.engine_run([])
        self.session(run, "r1s1", "## Next\nLONG: long_search.py | 1.5 h | decides a(15)\nLONG: long_gone.py | 1 | x\n",
                     {"long_search.py": "print('RESULT: none')\n"})
        reqs = R.long_requests(run, set())
        self.assertEqual([(r["key"], r["hours"], r["purpose"]) for r in reqs], [("r1s1/long_search.py", 1.5, "decides a(15)")])
        self.assertEqual(R.long_requests(run, {"r1s1/long_search.py"}), [])

    def test_a_computation_runs_without_a_model_and_its_output_reaches_the_library(self):
        run = self.engine_run([])
        self.session(run, "deep", "LONG: long_count.py | 0.1 | counts to three\n",
                     {"long_count.py": "for i in range(3):\n    print('progress', i)\nprint('RESULT: three')\n"})
        p = {"history": [], "kind": "record"}
        R.save_state({"problems": {"9": p}})
        ran = R.run_long(9, p, run, R.load_cfg())
        self.assertEqual([(r["status"], r["result"]) for r in ran], [("completed", True)])
        text = (self.d / "library" / "9" / "COMPUTE.md").read_text()
        self.assertIn("RESULT: three", text)
        self.assertIn("evidence, not a result", text)
        self.assertEqual(R.load_state()["problems"]["9"]["computed"], ["deep/long_count.py"])
        self.assertEqual(R.run_long(9, R.load_state()["problems"]["9"], run, R.load_cfg()), [])     # never twice

    def test_a_result_earns_one_follow_up_pass(self):
        run = self.engine_run([])
        self.session(run, "r1s1", "LONG: long_x.py | 0.1 | x\n", {"long_x.py": "print('RESULT: a(15) = 52')\n"})
        R.save_state({"problems": {"9": {"history": [], "kind": "record", "running": "scout", "run_dir": str(run),
                                         "prepped": True, "next": None}}})
        fake = lambda *a, **k: ({"run_dir": str(run.relative_to(self.d)), "spend_run": 5.0}, 0)
        with patch.object(R, "ROOT", self.d), patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: []), \
                patch.object(R, "classify", lambda rd: ("none", {})), patch.object(R, "record_atlas"), patch.object(R, "commit"):
            R.step(R.load_cfg())
        p = R.load_state()["problems"]["9"]
        self.assertEqual((p["next"], p["status"], p["followups"]), ("deep", "compute-followup", 1))

    def test_the_engine_reads_the_computation_after_the_digest(self):
        import harness as H
        lib = self.d / "library" / "9"
        lib.mkdir(parents=True)
        (lib / "DIGEST.md").write_text("the page")
        (lib / "COMPUTE.md").write_text("## Long computation\nRESULT: three")
        h = H.Harness.__new__(H.Harness)
        h.args = type("A", (), {"library": str(lib)})()
        h.log = type("L", (), {"event": lambda *a, **k: None})()
        text = h._library_text()
        self.assertLess(text.index("the page"), text.index("RESULT: three"))


class Persistence(Base):
    """2026-10-15, operator's direction: pursue the selected problems while passes make progress, and give the screened-out
    ones another screen with the repaired context."""

    def test_program_passes_scale_their_cycles_and_budget_and_extend_the_last(self):
        cfg = R.load_cfg()
        first = R.stage_flags(cfg, "program", {})
        self.assertIn("--engine-program-cycles 6 ", first)
        self.assertNotIn("--engine-program-extend", first)
        third = R.stage_flags(cfg, "program", {"program_passes": 2})
        self.assertIn("--engine-program-cycles 18 ", third)
        self.assertIn("--engine-program-budget 240 ", third)
        self.assertTrue(third.endswith("--engine-program-extend"))
        self.assertIn("--engine-objective record", R.stage_flags(cfg, "program", {"program_passes": 1, "kind": "record"}))

    def program_pass(self, validated_before, n_new, spend=50.0, passes=0):
        run = self.engine_run([])
        R.save_state({"problems": {"9": {"history": [], "next": "program", "run_dir": str(run), "track": "new-math",
                                         "spend": spend, "validated_seen": validated_before, "program_passes": passes}}})
        fake = lambda *a, **k: ({"run_dir": str(run.relative_to(self.d)), "spend_run": spend + 60.0}, 0)
        with patch.object(R, "ROOT", self.d), patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: []), \
                patch.object(R, "classify", lambda rd: ("traction", {})), patch.object(R, "record_atlas"), \
                patch.object(R, "commit"), patch.object(R, "validated_summary", lambda rd: (n_new, [1] * n_new, "")):
            R.step(R.load_cfg())
        return R.load_state()["problems"]["9"]

    def test_progress_earns_another_pass_and_none_ends_it(self):
        p = self.program_pass(validated_before=2, n_new=5)
        self.assertEqual((p["next"], p["status"], p["program_passes"]), ("program", "persist", 1))
        p = self.program_pass(validated_before=5, n_new=5)
        self.assertIsNone(p["next"])

    def test_the_caps_end_persistence(self):
        self.assertIsNone(self.program_pass(validated_before=0, n_new=3, spend=240.0)["next"])     # over max_spend
        self.assertIsNone(self.program_pass(validated_before=0, n_new=3, passes=2)["next"])        # the third pass

    def test_a_rescreen_is_a_new_screen_under_the_best_objective(self):
        (self.d / "survey.json").write_text(json.dumps({"records": [], "explicit": [{"problem": 1094, "score": 4.0, "claims": 0}]}))
        R.save_state({"problems": {"1094": {"status": "screened out", "run_dir": "runs/old", "settle_chance": 0.01,
                                            "spend": 5.4, "prepped": True, "history": []},
                                   "32": {"status": "screened out", "run_dir": "runs/o32", "prepped": True, "history": []},
                                   "655": {"status": "verified", "history": []}}})
        with patch.object(R, "write_library", lambda n: None):
            self.assertIn("as explicit", R.rescreen(1094))
            self.assertIn("as settle", R.rescreen(32))
            self.assertIn("not a screened-out problem", R.rescreen(655))
        st = R.load_state()
        p = st["problems"]["1094"]
        self.assertEqual((p["kind"], p["next"], p["spend"], p["previous"]["run_dir"]), ("explicit", "screen", 0.0, "runs/old"))
        self.assertEqual(R.next_action(st, R.load_cfg())[0], "screen")

    def test_persist_respects_the_claims_rule(self):
        R.save_state({"problems": {"1207": {"status": "done", "run_dir": "runs/r", "history": []},
                                   "366": {"status": "done", "run_dir": "runs/s", "history": []}}})
        with patch.object(R, "write_library", lambda n: None), patch.object(R, "site_claims", lambda n: 1 if n == 366 else 0):
            self.assertIn("research-program pass is next", R.persist(1207))
            self.assertIn("claims rule", R.persist(366))
        self.assertEqual(R.load_state()["problems"]["1207"]["next"], "program")


class LiteratureFindings(Base):
    def test_a_run_the_gate_stopped_is_a_known_result_and_never_retried(self):
        run = self.engine_run([])
        ej = json.loads((run / "engine" / "engine.json").read_text())
        ej.update({"stopped": "resolved in the literature", "literature": {"verdict": {
            "settled": True, "work": "An affirmative answer to Owings's sumset question", "why": "it proves it", "confidence": 0.95}}})
        (run / "engine" / "engine.json").write_text(json.dumps(ej))
        R.save_state({"problems": {"1199": {"history": [], "running": "screen", "prepped": True, "run_dir": str(run)}}})
        fake = lambda *a, **k: ({"run_dir": str(run.relative_to(self.d)), "spend_run": 0.4}, 0)
        with patch.object(R, "ROOT", self.d), patch.object(R, "run_screen", fake), patch.object(R, "queue", lambda s, c: []), \
                patch.object(R, "record_atlas") as atlas, patch.object(R, "commit"):
            R.step(R.load_cfg())
            self.assertEqual(R.next_action(R.load_state(), R.load_cfg()), ("idle", None))      # never attacked again
        p = R.load_state()["problems"]["1199"]
        self.assertEqual((p["status"], p["next"], p["track"]), ("known-result", None, "statement"))
        self.assertIn("Owings", p["resolved_in_literature"])
        self.assertIn("SETTLED in a paper", atlas.call_args[0][1])

    def test_every_paid_stage_runs_the_gate(self):
        cfg = R.load_cfg()
        for stage in ("screen", "scout", "deep", "program"):
            self.assertIn("--engine-literature-scan", R.stage_flags(cfg, stage, {}), stage)


ORIGINAL_SITE_CLAIMS = R.site_claims
ORIGINAL_REFRESH_SOURCES = R.refresh_sources
ORIGINAL_FRESH_TARGETS = R.fresh_targets


class Digest(unittest.TestCase):
    """The engine's problem digest carries the page's notes and the proof claims. Until 2026-10-14 both were cut on
    markers the pages lack, and #769's 'new' Lean-verified disproof was a weaker form of two claims posted there."""

    def test_page_notes_and_proof_claims_reach_the_digest(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location("od_screen", Path(R.__file__).parent / "experiments" /
                                                      "open-discovery-2026-10-02" / "screen.py")
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "atlas-data" / "forum").mkdir(parents=True)
            nav = "Forum\n Inbox\n Go\n Go\n Random\n"
            thread = (nav + "Let c(n) be minimal such that ...\n#9: [Er74b]\nHudelson proved c(n) < 6^n.\n Proof expositions (0)\n"
                      " Order by\n oldest first\n Best bounds are due to Connor and Marmorino.\n")
            claims = (nav + "Let c(n) be minimal such that ...\n There are 2 proof claims (partial or full) for this problem.\n"
                      "A proof \nclaimed by Jeffrey Zeng (using an OpenAI internal model).\n Summary:\n c(n) = o(n^n).\n")
            (Path(tmp) / "atlas-data" / "forum" / "9.json").write_text(json.dumps({"thread": thread, "claims": claims,
                                                                                     "fetched": "2026-10-14"}))
            with patch.object(m, "ROOT", Path(tmp)):
                text = m.thread_digest("9")
        page = text.split("## Page\n")[1].split("## Forum comments")[0]
        self.assertIn("Hudelson proved", page)
        self.assertNotIn("Inbox", page)                                  # the navigation is not the page
        self.assertIn("Connor and Marmorino", text)
        self.assertIn("## Proof claims page\nThere are 2 proof claims", text)
        self.assertIn("claimed by Jeffrey Zeng", text)


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

    def fc_and_run(self):
        """A formal-conjectures file at the pinned commit and an engine run frozen from it, as the screen freezes."""
        import timesplit as T
        (self.d / "fc").mkdir(exist_ok=True)
        (self.d / "fc" / "99.lean").write_text("/-- Q. -/\n@[category research open]\ntheorem erdos_99 : True := by\n  sorry\n")
        run = self.engine_run([])
        st = json.loads((run / "state.json").read_text())
        st["statement"] = T.frozen_statement(T.parse_fc((self.d / "fc" / "99.lean").read_text(), 99), 99)
        (run / "state.json").write_text(json.dumps(st))
        return run

    def frozen(self, ok=True):
        return {"ok": ok, "statement": "def V : Prop := True\n\ntheorem erdos_99 : True := by\n  sorry",
                "imports": ["Mathlib.Tactic", "Mathlib.Geometry.Euclidean.Basic"], "inlined": ["V"], "classical": False,
                "files": ["FormalConjecturesForMathlib/V.lean"], "errors": [] if ok else ["unknown namespace `EuclideanGeometry`"],
                "decls": [{"name": "V", "file": "FormalConjecturesForMathlib/V.lean", "text": "def V : Prop := True"}]}

    def test_a_statement_that_cannot_compile_blocks_the_stage_before_any_spend(self):
        # 2026-10-14: #655's Lean stage ended after $0.06 on `unknown namespace EuclideanGeometry`
        import timesplit as T
        run = self.fc_and_run()
        complete = {"claim": "deep/C1", "answer": "true", "statement": "s", "intent": "new-math"}
        R.save_state({"problems": {"99": {"history": [], "next": "lean", "run_dir": str(run), "complete": complete}}})
        launched = []
        with patch.object(R, "ROOT", self.d), patch.object(T, "freeze_compiling", lambda *a, **k: self.frozen(False)), \
                patch("harness.decl_index", lambda: None), patch.object(R, "commit"), patch.object(R, "queue", lambda s, c: []), \
                patch.object(R, "run_lean", lambda *a, **k: launched.append(a) or (0, "")):
            R.step(R.load_cfg())
        p = R.load_state()["problems"]["99"]
        self.assertEqual((p["status"], p["next"], p["running"]), ("lean-blocked", None, None))
        self.assertIn("EuclideanGeometry", p["lean_blocked"])
        self.assertFalse(launched)
        self.assertIsNone(p.get("lean_run"))
        self.assertEqual(json.loads(R.RESULTS.read_text().splitlines()[-1])["outcome"], "blocked")

    def test_an_inlined_definition_must_read_the_same_at_the_campaigns_commit(self):
        import timesplit as T
        run = self.fc_and_run()
        pages = {"same": "/-- doc -/\ndef V : Prop := True\n", "changed": "def V : Prop := False\n"}
        for page, ok in (("same", True), ("changed", False)):
            with patch.object(T, "freeze_compiling", lambda *a, **k: self.frozen()), patch("harness.decl_index", lambda: None), \
                    patch.object(T, "fetch", lambda url, dest, **k: pages[page]):
                r = R.lean_statement(99, run, {"fc_sha": "abc"})
            self.assertEqual(r["ok"], ok, page)
        self.assertIn("reads differently at the pinned commit", r["why"])

    def test_the_built_run_carries_the_compiling_statement_and_its_imports(self):
        run = self.engine_run([_claim("deep", "C1", "validated-new", 3, statement="it holds")])
        with patch.object(R, "ROOT", self.d):
            lean = R.build_lean_run(99, run, "deep/C1", "true", self.frozen())
        self.assertEqual(json.loads((lean / "problem.json").read_text())["imports"][-1], "Mathlib.Geometry.Euclidean.Basic")
        st = json.loads((lean / "state.json").read_text())
        self.assertTrue(st["statement"].startswith("def V"))
        self.assertIn("made to compile by resolution.lean_statement", st["statement_source"])
        self.assertIn("inlined from formal-conjectures V", st["statement_source"])

    def test_an_operator_can_send_a_complete_answer_back_to_lean(self):
        complete = {"claim": "deep/C1", "answer": "false", "statement": "s", "intent": "formalization-gap"}
        R.save_state({"problems": {"655": {"history": [], "status": "lean-partial", "next": None, "complete": complete,
                                           "lean_run": "runs/old"}, "7": {"history": [], "running": "scout"}}})
        self.assertIn("back to the Lean stage", R.requeue_lean(655))
        p = R.load_state()["problems"]["655"]
        self.assertEqual((p["next"], p["status"], p["lean_run"]), ("lean", "complete", None))
        self.assertEqual(p["history"][-1]["previous"], "runs/old")
        self.assertEqual(R.next_action(R.load_state(), R.load_cfg()), ("lean", 655))
        self.assertIn("no complete answer", R.requeue_lean(7))

    def test_a_verified_result_is_flagged_for_review(self):
        run = self.engine_run([])
        with patch.object(R, "ROOT", self.d):
            R.flag_for_review(99, run, "RUN-SUMMARY problem=99 exit=0", "deep/C1", run)
        text = R.REVIEW.read_text()
        self.assertIn("independent human review", text)
        self.assertIn("## #99", text)


if __name__ == "__main__":
    unittest.main()
