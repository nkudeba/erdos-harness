"""The free specialist cascade (real Lean part opt-in: DEDUCTIVE_LEAN_TESTS=1; ERDOS_LEAN_PROJECT names a built Lean
project when the checkout has none, e.g. in a git worktree).

Every alternative must close its goal. Unguarded, `first | … | (simp_all) | …` accepts a `simp_all` that only
simplifies. The tactics after it never run, and Lean reports the leftover goal at the enclosing `by`, a line above the
hole. `_close_holes_without_model` attributes errors by line, so it read the hole as closed; the keep-check then failed
and reverted the whole pass, genuine closures included. A replay of 41 saved passes
(benchmarks/timesplit/analysis/cascade_replay.py) found 71 holes read as closed and 0 actually closed.

Two more defects, fixed 2026-10-15:
- Lean counts lines in the composed file, 8 header lines above the body, and the cascade compared those lines with body
  lines. A pass in which some holes closed and others did not read every hole as closed and kept none.
- `exact?` gives its suggestion as an info message, which Lean's plain output prints with no `file:line:col:` prefix, so
  `LeanChecker._parse` never recorded one and the `exact?` pass closed nothing. It now compiles with `lean --json`.
  `exact?` also cites the file's own open hypotheses, which only moves a hole, so such a suggestion is refused.
"""
import argparse, json, os, re, subprocess, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

# tactics that can succeed while leaving the goal open
MAY_LEAVE_GOALS = {"simp", "simp_all", "norm_num", "aesop", "field_simp", "ring_nf", "simp_arith", "push_cast"}
OLD_CASCADE = "first | omega | (simp_all) | positivity | (norm_num) | (nlinarith) | (decide +kernel) | (aesop)"

# `hyp_a` closes outright; `hyp_c` is the trap: simp_all only strips `+ 0`, and positivity closes it
SKELETON = """theorem erdos_98_hyp_a : ∀ n : ℕ, n + 0 = n := by
  sorry

theorem erdos_98_hyp_c (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * x + x + 0 := by
  sorry

theorem erdos_98 : True := by
  trivial"""

# the tactics close `hyp_easy` and nothing closes `hyp_hard`: the pass must keep the one closure it found
PARTIAL = """theorem erdos_98_hyp_easy : ∀ n : ℕ, n + 0 = n := by
  sorry

theorem erdos_98_hyp_hard : ∀ n : ℕ, n ^ 2 ≠ 2 := by
  sorry

theorem erdos_98 : True := by
  trivial"""

# only `exact?` closes `hyp_g`; `exact?` "closes" `hyp_twin` by citing the open `hyp_hard`, which must be refused
EXACT = """theorem erdos_98_hyp_hard : ∀ n : ℕ, n ^ 2 ≠ 2 := by
  sorry

theorem erdos_98_hyp_twin : ∀ n : ℕ, n ^ 2 ≠ 2 := by
  sorry

theorem erdos_98_hyp_g : ∀ a b : ℕ, Nat.gcd a b = Nat.gcd b a := by
  sorry

theorem erdos_98 : True := by
  trivial"""


class CascadeShape(unittest.TestCase):
    def test_every_alternative_that_can_leave_a_goal_is_guarded(self):
        body = H.Harness.CASCADE.strip()
        self.assertTrue(body.startswith("first "))
        alts = [a.strip() for a in body[len("first"):].split("|") if a.strip()]
        self.assertGreater(len(alts), 3)
        for alt in alts:
            head = alt.strip("() ").split(";")[0].split()[0]
            if head in MAY_LEAVE_GOALS:
                self.assertRegex(alt, r";\s*done\)?$", f"`{alt}` can succeed without closing its goal")


class Log:
    def __init__(self):
        self.events = []

    def event(self, stage, event, **kw):
        self.events.append((stage, event, kw))


def _closed(h, by=None):
    return [e[2] for e in h.log.events if e[1] == "hole_closed" and (by is None or e[2]["by"] == by)]


class FakeLean:
    """Lean as the cascade meets it, without Lean: positions count the composed file (the import header sits above the
    body), an info message has no position in plain output, and `positions=True` (`lean --json`) gives every message
    its line and column. A theorem in `closes` falls to the tactic cascade; `suggests[name]` lists what `exact?`
    suggests for that theorem's holes, in order; a closure text in `broken` fails to compile."""

    def __init__(self, h, closes=(), suggests=None, broken=(), timeout=()):
        self.h, self.closes, self.suggests, self.broken, self.timeout = h, set(closes), suggests or {}, set(broken), set(timeout)
        self.calls = []

    def __call__(self, body, name, positions=False):
        self.calls.append(name)
        if name in self.timeout:
            return {"ok": False, "timeout": True, "errors": ["lean check timed out after 9s"], "warnings": [],
                    "infos": [], "sorries": False, "raw": "", "body": body}
        at = {b: c for c, b in H.compose_line_map(body, self.h.imports).items()}     # body line -> composed line
        errors, msgs, owner, seen = [], [], None, {}
        for ln, line in enumerate(body.split("\n"), 1):
            m = re.match(r"theorem (\S+)", line)
            owner = m.group(1) if m else owner
            for t in re.finditer(re.escape(H.Harness.CASCADE), line):
                if owner not in self.closes:
                    errors.append(f"line {at[ln]}:{t.start()}: linarith failed")
            for t in re.finditer(r"exact\?", line):
                i = seen[owner] = seen.get(owner, -1) + 1
                sugg = (self.suggests.get(owner) or [])[i:i + 1]
                if sugg:
                    msgs.append({"line": at[ln], "col": t.start(), "sev": "info", "msg": f"Try this:\n  [apply] {sugg[0]}"})
                else:
                    errors.append(f"line {at[ln]}:{t.start()}: `exact?` could not close the goal.")
            for b in self.broken:
                if b in line and "exact?" not in line:
                    errors.append(f"line {at[ln]}:2: type mismatch")
        res = {"ok": not errors, "timeout": False, "errors": errors, "warnings": [], "infos": [],
               "sorries": bool(H.hole_count(body)), "body": body,
               "raw": "".join(m["msg"] + "\n" for m in msgs) + "".join(f"f.lean:{e[5:]}\n" for e in errors)}
        if positions:
            res["messages"] = msgs
        return res


def _harness(**fake):
    h = H.Harness.__new__(H.Harness)
    h.log = Log()
    h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
    h.imports = list(H.DEFAULT_IMPORTS)
    h.check = FakeLean(h, **fake)
    return h


class CascadeAttribution(unittest.TestCase):
    """The cascade's bookkeeping against a fake Lean that reports positions the way Lean does."""

    def test_a_partial_pass_keeps_the_hole_it_closed(self):
        h = _harness(closes={"erdos_98_hyp_easy"})
        out = h._close_holes_without_model(PARTIAL, "")
        self.assertEqual(H.hole_count(out), 1, out)
        self.assertIn(H.Harness.CASCADE, out.split("theorem erdos_98_hyp_hard")[0])
        self.assertIn("sorry", out.split("theorem erdos_98_hyp_hard")[1])
        self.assertEqual([e["line"] for e in _closed(h, "specialist-cascade")], [2])
        self.assertEqual(h.check.calls, ["cascade", "cascade-keep", "cascade-exact"])

    def test_a_pass_that_closes_every_hole_needs_no_keep_compile(self):
        h = _harness(closes={"erdos_98_hyp_easy", "erdos_98_hyp_hard"})
        out = h._close_holes_without_model(PARTIAL, "")
        self.assertEqual(H.hole_count(out), 0)
        self.assertEqual(h.check.calls, ["cascade"])

    def test_a_line_the_composed_file_moved_is_still_attributed(self):
        # a dropped mid-body line shifts every line below it by one more than the header does
        code = PARTIAL.replace("theorem erdos_98_hyp_hard", "set_option maxHeartbeats 400000 in\ntheorem erdos_98_hyp_hard")
        h = _harness(closes={"erdos_98_hyp_easy"})
        out = h._close_holes_without_model(code, "")
        self.assertEqual(H.hole_count(out), 1, out)
        self.assertEqual(len(_closed(h, "specialist-cascade")), 1)

    def test_a_timeout_closes_nothing(self):
        h = _harness(closes={"erdos_98_hyp_easy"}, timeout={"cascade", "cascade-exact"})
        self.assertEqual(h._close_holes_without_model(PARTIAL, ""), PARTIAL)
        self.assertEqual(_closed(h), [])

    def test_exact_suggestions_are_read_from_positions_and_kept(self):
        h = _harness(suggests={"erdos_98_hyp_g": ["exact fun a b => Nat.gcd_comm a b"]})
        out = h._close_holes_without_model(EXACT, "")
        self.assertIn("exact fun a b => Nat.gcd_comm a b", out)
        self.assertEqual(H.hole_count(out), 2)
        self.assertEqual([(e["line"], e["by"]) for e in _closed(h)], [(8, "exact?")])
        self.assertEqual(h.check.calls, ["cascade", "cascade-exact", "cascade-exact-keep"])

    def test_two_holes_on_one_line_take_their_own_suggestions(self):
        code = ("theorem erdos_98_hyp_pair (x : ℕ) : x * 1 = x ∧ x + 0 = x := ⟨(by sorry), (by sorry)⟩\n\n"
                "theorem erdos_98_hyp_term : ∀ a b : ℕ, Nat.gcd a b = Nat.gcd b a := sorry\n\n"
                "theorem erdos_98 : True := by\n  trivial")
        h = _harness(suggests={"erdos_98_hyp_pair": ["exact Nat.mul_one x", "exact Nat.add_zero x"],
                               "erdos_98_hyp_term": ["exact fun a b => Nat.gcd_comm a b"]})
        out = h._close_holes_without_model(code, "")
        self.assertIn("⟨(by exact Nat.mul_one x), (by exact Nat.add_zero x)⟩", out)
        self.assertIn(":= (by exact fun a b => Nat.gcd_comm a b)", out)
        self.assertEqual(H.hole_count(out), 0)

    def test_a_suggestion_citing_an_open_hypothesis_is_refused(self):
        h = _harness(suggests={"erdos_98_hyp_twin": ["exact fun n => erdos_98_hyp_hard n"],
                               "erdos_98_hyp_g": ["exact fun a b => Nat.gcd_comm a b"]})
        out = h._close_holes_without_model(EXACT, "")
        self.assertNotIn("erdos_98_hyp_hard n", out)
        self.assertIn("Nat.gcd_comm", out)
        refused = [e[2] for e in h.log.events if e[1] == "exact_suggestion_refused"]
        self.assertEqual([(r["line"], r["cites"]) for r in refused], [(5, "erdos_98_hyp_hard")])

    def test_a_citation_of_a_hole_closed_in_the_same_pass_is_kept(self):
        code = EXACT.replace("theorem erdos_98_hyp_twin : ∀ n : ℕ, n ^ 2 ≠ 2", "theorem erdos_98_hyp_twin : True")
        code = code + "\n\ntheorem erdos_98_hyp_t (a b : ℕ) : Nat.gcd a b = Nat.gcd b a := by\n  sorry"
        h = _harness(suggests={"erdos_98_hyp_g": ["exact fun a b => Nat.gcd_comm a b"],
                               "erdos_98_hyp_t": ["exact erdos_98_hyp_g a b"]})
        out = h._close_holes_without_model(code, "")
        self.assertIn("exact erdos_98_hyp_g a b", out)
        self.assertEqual(H.hole_count(out), 2)                 # hyp_hard and hyp_twin

    def test_a_suggestion_that_does_not_compile_is_dropped_and_the_rest_kept(self):
        h = _harness(suggests={"erdos_98_hyp_twin": ["exact bogus_term"],
                               "erdos_98_hyp_g": ["exact fun a b => Nat.gcd_comm a b"]}, broken={"bogus_term"})
        out = h._close_holes_without_model(EXACT, "")
        self.assertNotIn("bogus_term", out)
        self.assertIn("Nat.gcd_comm", out)
        self.assertEqual(h.check.calls, ["cascade", "cascade-exact", "cascade-exact-keep", "cascade-exact-keep-retry"])

    def test_goals_are_extracted_at_the_holes_lines(self):
        h = _harness()

        def check(body, name, positions=False):
            at = {b: c for c, b in H.compose_line_map(body, h.imports).items()}
            errs = [f"line {at[n]}:2: unsolved goals\n⊢ goal of line {n}" for n, l in enumerate(body.split("\n"), 1)
                    if l.strip() == "done"]
            return {"ok": False, "errors": errs, "infos": [], "body": body}
        h.check = check
        spans = H.Harness._hole_spans(PARTIAL)
        self.assertEqual(h._extract_goals(PARTIAL, spans), {0: "⊢ goal of line 2", 1: "⊢ goal of line 5"})


class LeanOutput(unittest.TestCase):
    """What the checker makes of Lean's output (no Lean)."""

    JSON_OUT = "\n".join(json.dumps(d) for d in [
        {"caption": "", "data": "declaration uses `sorry`", "fileName": "/t/x.lean", "kind": "hasSorry",
         "pos": {"column": 8, "line": 9}, "severity": "warning"},
        {"caption": "", "data": "Try this:\n  [apply] exact fun a b => Nat.gcd_comm a b", "fileName": "/t/x.lean",
         "kind": "[anonymous]", "pos": {"column": 2, "line": 16}, "severity": "information"},
        {"caption": "", "data": "Unknown identifier `foo`", "fileName": "/t/x.lean",
         "kind": "lean.unknownIdentifier._namedError", "pos": {"column": 4, "line": 20}, "severity": "error"},
        {"caption": "", "data": "erdos_98_hyp_g : ∀ (a b : ℕ), a.gcd b = b.gcd a", "fileName": "/t/x.lean",
         "kind": "[anonymous]", "pos": {"column": 0, "line": 22}, "severity": "information"},
    ]) + "\nnot a message\n"

    def test_json_messages_keep_their_positions_and_the_plain_text(self):
        msgs, plain = H.LeanChecker._parse_json(self.JSON_OUT)
        self.assertEqual([(m["line"], m["col"], m["sev"]) for m in msgs],
                         [("9", "8", "warning"), ("16", "2", "info"), ("20", "4", "error"), ("22", "0", "info")])
        self.assertIn("/t/x.lean:20:4: error(lean.unknownIdentifier): Unknown identifier `foo`", plain)
        self.assertIn("Try this:\n  [apply] exact fun a b => Nat.gcd_comm a b\n", plain)
        self.assertIn("not a message", plain)
        # the plain text parses back the way Lean's own plain output does: the info message glued to the warning
        self.assertEqual([m["sev"] for m in H.LeanChecker(Path("."), 1)._parse(plain)], ["warning", "error"])

    def test_suggestions_parse_in_both_layouts(self):
        self.assertEqual(H.try_this_suggestion("Try this:\n  [apply] exact fun a b => Nat.gcd_comm a b"),
                         "exact fun a b => Nat.gcd_comm a b")
        self.assertEqual(H.try_this_suggestion("Try this: exact Nat.add_comm a b"), "exact Nat.add_comm a b")
        self.assertEqual(H.try_this_suggestion("Try this:\n  [apply] exact\n    fun a b =>\n      Nat.gcd_comm a b"),
                         "exact fun a b => Nat.gcd_comm a b")
        self.assertEqual(H.try_this_suggestion("Try these:\n  [apply] exact foo\n  [apply] exact bar"), "exact foo")
        self.assertIsNone(H.try_this_suggestion("erdos_98_hyp_g : ∀ (a b : ℕ), a.gcd b = b.gcd a"))

    def test_plain_output_suggestions_are_found_in_raw(self):
        raw = ("Try this:\n  [apply] exact fun a b => Nat.gcd_comm a b\n"
               "/t/x.lean:18:2: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.\n"
               "/t/x.lean:20:2: info: Try this: exact Nat.add_comm a b\n"
               "erdos_98_hyp_g : ∀ (a b : ℕ), a.gcd b = b.gcd a\n")
        self.assertEqual(H.try_this_blocks(raw), ["Try this: exact fun a b => Nat.gcd_comm a b",
                                                  "Try this: exact Nat.add_comm a b"])
        self.assertEqual(H.LeanChecker(Path("."), 1)._parse(raw)[0]["sev"], "error")   # why `infos` stays empty

    def test_the_line_map_follows_lines_compose_drops(self):
        body = "\n\nimport Mathlib.Tactic\ntheorem a : True := by\n  trivial\nset_option maxHeartbeats 400000 in\ntheorem b : True := by\n  sorry"
        src, lmap = H.compose(body, list(H.DEFAULT_IMPORTS)), H.compose_line_map(body, list(H.DEFAULT_IMPORTS))
        self.assertEqual(sorted(lmap.values()), [4, 5, 7, 8])
        for c, b in lmap.items():
            self.assertEqual(src.split("\n")[c - 1].strip(), body.split("\n")[b - 1].strip())
        self.assertEqual(H.error_lines(["line 12:2: unsolved goals", "line 3:0: header"], lmap), {8})

    def test_blank_comments_keeps_every_offset(self):
        s = '/-- theorem fake : True := sorry -/\nnotation "ℝ²" => ℕ\n-- theorem gone\ntheorem real : True := trivial'
        b = H.blank_comments(s)
        self.assertEqual(len(b), len(s))
        self.assertEqual(b.index("theorem real"), s.index("theorem real"))
        self.assertNotIn("fake", b)
        self.assertNotIn("gone", b)

    def test_a_timeout_with_an_error_in_the_partial_output_is_reported(self):
        # the timeout branch read a "text" key `_parse` never sets, and raised KeyError
        class Proc:
            pid, args = 0, []

            def __init__(self, *a, **k):
                self.first = True

            def communicate(self, timeout=None):
                if self.first:
                    self.first = False
                    raise subprocess.TimeoutExpired("lean", timeout, output="/t/x.lean:3:2: error: unsolved goals\n⊢ False\n")
                return "/t/x.lean:3:2: error: unsolved goals\n⊢ False\n", ""
        saved = (H.subprocess.Popen, H.os.killpg)
        H.subprocess.Popen, H.os.killpg = Proc, lambda *a: None
        try:
            with tempfile.TemporaryDirectory() as tmp:
                res = H.LeanChecker(Path(tmp), 1).check("theorem x : False := by\n  skip", Path(tmp) / "x.lean")
        finally:
            H.subprocess.Popen, H.os.killpg = saved
        self.assertTrue(res["timeout"])
        self.assertEqual(res["errors"][1], "line 3:2: unsolved goals\n⊢ False")


def _lean_project() -> Path:
    return Path(os.environ.get("ERDOS_LEAN_PROJECT") or H.FORMAL)


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class CascadeInLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        proj = _lean_project()
        self._saved = (H.FORMAL, H.MATHLIB_SRC, H._INDEX, dict(H._decl_cache))
        if proj != H.FORMAL:                       # a worktree: point the index and module checks at the built project
            H.FORMAL, H.MATHLIB_SRC = proj, proj / ".lake" / "packages" / "mathlib" / "Mathlib"
            H._INDEX, H._decl_cache = H.DeclIndex(), {}
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "98", "statement": "cascade", "tags": []}
        h.state = {}
        h.log = Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS) + ["Mathlib.Tactic"], []
        h.lean = H.LeanChecker(proj, 600)
        h._lock = threading.Lock()
        h.checks = 0
        self.h = h
        self.frozen = H.statement_prefix("theorem erdos_98 : True := by\n  sorry")

    def tearDown(self):
        H.FORMAL, H.MATHLIB_SRC, H._INDEX, cache = self._saved
        H._decl_cache.clear()
        H._decl_cache.update(cache)
        self.tmp.cleanup()

    def test_the_old_string_misreads_one_hole_and_reverts_the_other(self):
        self.h.CASCADE = OLD_CASCADE                    # instance attribute shadows the class's fixed string
        self.h._close_holes_without_model(SKELETON, self.frozen)
        # hyp_a's genuine closure was reverted with hyp_c's false one (exact? may close either afterwards)
        self.assertEqual(_closed(self.h, "specialist-cascade"), [])

    def test_the_guarded_cascade_closes_both(self):
        out = self.h._close_holes_without_model(SKELETON, self.frozen)
        self.assertEqual(H.hole_count(out), 0, out)
        res = self.h.check(out, "closed")
        self.assertTrue(res["ok"], res["errors"][:2])
        self.assertFalse(res["sorries"])

    def test_a_partial_pass_keeps_what_it_closed(self):
        out = self.h._close_holes_without_model(PARTIAL, self.frozen)
        self.assertEqual(H.hole_count(out), 1, out)                  # both kept their sorry before the fix
        self.assertIn("sorry", out.split("theorem erdos_98_hyp_hard")[1])
        self.assertEqual([e["line"] for e in _closed(self.h, "specialist-cascade")], [2])

    def test_exact_closes_what_the_tactics_cannot_and_refuses_an_open_citation(self):
        out = self.h._close_holes_without_model(EXACT, self.frozen)
        self.assertIn("Nat.gcd_comm", out)                           # nothing was ever read from `exact?` before the fix
        self.assertEqual(H.hole_count(out), 2, out)                  # hyp_hard, and hyp_twin's citation of it refused
        refused = [e[2] for e in self.h.log.events if e[1] == "exact_suggestion_refused"]
        self.assertEqual([r["cites"] for r in refused], ["erdos_98_hyp_hard"], self.h.log.events)
        res = self.h.check(out, "closed")
        self.assertTrue(res["ok"], res["errors"][:2])


if __name__ == "__main__":
    unittest.main()
