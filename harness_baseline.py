#!/usr/bin/env python3
"""
erdos-harness — an LLM + Lean 4 harness for attempting Erdős problems.

Pipeline:
    literature -> formalize -> crosscheck -> prove (rounds) -> [decompose] -> verify -> report

Design principles:
  * Lean is the ground truth: nothing counts unless `lake env lean` accepts it.
  * The LLM is sampled, never trusted: every artifact is compiled and errors are
    fed back into the next round.
  * The formal statement is frozen after cross-checking: provers may add helper
    lemmas above it but may not alter the theorem being proved (enforced by a
    normalized-substring guard).
  * Verification is layered: clean compile + no `sorry` + `#print axioms` +
    blind back-translation of the formal statement.

LLM backends:
  * claude-cli : shells out to `claude -p` (requires a logged-in Claude Code CLI).
  * file       : writes each prompt to <run>/llm/pending/<id>.json and blocks
                 until <run>/llm/done/<id>.txt appears — lets any external agent
                 (or human) serve completions. Used for driving the harness from
                 an outer agent session.

Usage:
    python3 harness.py run --problem problems/erdos_NNN.json [--backend file|claude-cli]
                           [--samples 3] [--rounds 6] [--skip-literature] [--resume RUN_DIR]
    python3 harness.py check path/to/File.lean
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formal"
RUNS = ROOT / "runs"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Full `import Mathlib` costs ~6 min/check on a 16GB laptop; a curated set costs ~30s.
# Problems can override via an "imports" field; models can request more via `-- IMPORTS:`.
DEFAULT_IMPORTS = [
    "Mathlib.Tactic.NormNum.Basic",
    "Mathlib.Tactic.Ring",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Algebra.BigOperators.Fin",
    "Mathlib.Data.Nat.Factorial.Basic",
]
IMPORT_RE = re.compile(r"^Mathlib(\.[A-Za-z0-9'!?]+)+$")
BANNED_IN_PROOFS = ["sorry", "admit", "native_decide", "\naxiom ", "unsafe ", "sorryAx"]
COMPILE_WORKERS = 3


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def clean_env() -> dict:
    home = os.environ.get("HOME", str(Path.home()))
    return {
        "HOME": home,
        "PATH": f"{home}/.elan/bin:{home}/.local/bin:/usr/local/bin:/usr/bin:/bin",
        "USER": os.environ.get("USER", "user"),
        "TERM": "dumb",
        "LANG": "en_US.UTF-8",
    }


class RunLog:
    def __init__(self, run_dir: Path):
        self.path = run_dir / "log.jsonl"

    def event(self, stage: str, event: str, **data):
        rec = {"ts": now(), "stage": stage, "event": event, **data}
        with open(self.path, "a") as f:
            f.write(json.dumps(rec) + "\n")
        brief = {k: (v[:160] + "…" if isinstance(v, str) and len(v) > 160 else v) for k, v in data.items()}
        print(f"[{rec['ts']}] {stage}/{event} {brief}", flush=True)


# --------------------------------------------------------------------------- LLM backends

class ClaudeCliBackend:
    """Production backend: `claude -p` in print mode with a scrubbed environment."""

    def __init__(self, model: str | None, timeout: int):
        self.model = model
        self.timeout = timeout
        self.bin = shutil.which("claude") or f"{os.environ['HOME']}/.local/bin/claude"

    def complete(self, purpose: str, prompt: str) -> str:
        cmd = [self.bin, "-p", "--output-format", "text"]
        if self.model:
            cmd += ["--model", self.model]
        r = subprocess.run(cmd, input=prompt, capture_output=True, text=True,
                           timeout=self.timeout, env=clean_env())
        if r.returncode != 0:
            raise RuntimeError(f"claude -p failed ({purpose}): {r.stderr.strip()[:500]}")
        return r.stdout


class FileBackend:
    """Agent-served backend: request files out, completion files in."""

    def __init__(self, run_dir: Path, timeout: int):
        self.llm = run_dir / "llm"
        self.pending = self.llm / "pending"
        self.done = self.llm / "done"
        self.archive = self.llm / "archive"
        for d in (self.pending, self.done, self.archive):
            d.mkdir(parents=True, exist_ok=True)
        self.timeout = timeout
        seen = [p.name.split("-")[0] for d in (self.archive, self.pending) for p in d.glob("*.json")]
        seen += [p.name.split("-")[0] for p in self.done.glob("*.txt")]
        self.counter = max([int(x) for x in seen if x.isdigit()], default=0)

    def complete(self, purpose: str, prompt: str) -> str:
        self.counter += 1
        rid = f"{self.counter:03d}-{purpose}"
        req = self.pending / f"{rid}.json"
        resp = self.done / f"{rid}.txt"
        if resp.exists():
            resp.unlink()  # never consume a stale response from a prior invocation
        req.write_text(json.dumps({
            "id": rid, "purpose": purpose, "created_at": now(),
            "response_path": str(resp), "prompt": prompt,
        }, indent=2))
        deadline = time.time() + self.timeout
        while time.time() < deadline:
            if resp.exists():
                time.sleep(1.0)  # let the writer finish
                text = resp.read_text()
                shutil.move(str(req), self.archive / req.name)
                return text
            time.sleep(3)
        raise TimeoutError(f"no response for {rid} within {self.timeout}s")


# --------------------------------------------------------------------------- Lean

class LeanChecker:
    MSG_RE = re.compile(r"^(?P<path>[^\s:][^:\n]*):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info): ?(?P<msg>.*)$")

    def __init__(self, project: Path, timeout: int):
        self.project = project
        self.timeout = timeout

    def check(self, source: str, dest: Path) -> dict:
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(source)
        try:
            r = subprocess.run(["lake", "env", "lean", str(dest)],
                               cwd=self.project, capture_output=True, text=True,
                               timeout=self.timeout, env=clean_env())
        except subprocess.TimeoutExpired:
            return {"ok": False, "timeout": True, "errors": [f"lean check timed out after {self.timeout}s"],
                    "warnings": [], "infos": [], "sorries": False, "raw": ""}
        msgs = self._parse(r.stdout + "\n" + r.stderr)
        errors = [m for m in msgs if m["sev"] == "error"]
        warnings = [m for m in msgs if m["sev"] == "warning"]
        infos = [m for m in msgs if m["sev"] == "info"]
        # Lean's quote style around `sorry` varies across versions; match loosely.
        sorries = any("declaration uses" in m["msg"] and "sorry" in m["msg"] for m in warnings)
        return {
            "ok": r.returncode == 0 and not errors,
            "timeout": False,
            "errors": [f"line {m['line']}:{m['col']}: {m['msg'][:600]}" for m in errors],
            "warnings": [f"line {m['line']}:{m['col']}: {m['msg'][:300]}" for m in warnings],
            "infos": [f"line {m['line']}:{m['col']}: {m['msg'][:300]}" for m in infos],
            "sorries": sorries,
            "raw": (r.stdout + r.stderr)[:20000],
        }

    def _parse(self, out: str) -> list[dict]:
        msgs = []
        for line in out.splitlines():
            m = self.MSG_RE.match(line)
            if m:
                msgs.append({"line": m["line"], "col": m["col"], "sev": m["sev"], "msg": m["msg"]})
            elif msgs and line.strip():
                msgs[-1]["msg"] += "\n" + line
        return msgs


# --------------------------------------------------------------------------- retrieval

def loogle(query: str, limit: int = 8) -> list[str]:
    try:
        url = "https://loogle.lean-lang.org/json?q=" + urllib.parse.quote(query)
        with urllib.request.urlopen(url, timeout=20) as r:
            data = json.loads(r.read().decode())
        hits = data.get("hits") or []
        return [f"{h.get('name')} : {h.get('type', '?')}  [{h.get('module', '?')}]" for h in hits[:limit]]
    except Exception:
        return []


def grep_mathlib(pattern: str, limit: int = 12) -> list[str]:
    src = FORMAL / ".lake" / "packages" / "mathlib" / "Mathlib"
    if not src.exists():
        return []
    try:
        r = subprocess.run(["grep", "-rInE", "--include=*.lean", pattern, str(src)],
                           capture_output=True, text=True, timeout=60, env=clean_env())
        lines = [l.replace(str(src), "Mathlib") for l in r.stdout.splitlines()]
        return lines[:limit]
    except Exception:
        return []


def run_retrieval_directives(text: str) -> list[str]:
    """Attempts may embed `-- LOOGLE: <q>` / `-- GREP: <regex>` comments; execute them."""
    out = []
    for q in re.findall(r"^--\s*LOOGLE:\s*(.+)$", text, re.M)[:4]:
        hits = loogle(q.strip())
        out.append(f"loogle `{q.strip()}`:\n  " + ("\n  ".join(hits) if hits else "(no hits)"))
    for q in re.findall(r"^--\s*GREP:\s*(.+)$", text, re.M)[:4]:
        hits = grep_mathlib(q.strip())
        out.append(f"grep `{q.strip()}`:\n  " + ("\n  ".join(hits) if hits else "(no hits)"))
    return out


# --------------------------------------------------------------------------- prompts

HOUSE_RULES = """\
Rules for all Lean code you produce:
- Lean 4 with current Mathlib master. Use Mathlib4 names (Nat.succ_le_iff, Finset.card_le_card, ZMod, ...).
- Put code ONLY inside ```lean fenced blocks. No prose inside the blocks.
- Do NOT write `import` lines — the harness provides a curated import header (listed in the task).
  If you need another Mathlib module, put `-- IMPORTS: Mathlib.Foo.Bar` on its own line INSIDE your
  ```lean block and the harness will add it to the header.
- Never use `axiom`, `native_decide`, `unsafe`, or metaprogramming escapes.
- Useful tactics: norm_num, decide, omega, simp/simp_all, ring, field_simp, positivity, gcongr,
  nlinarith, interval_cases, induction, strong induction via Nat.strong_induction_on, rcases/obtain,
  Finset reasoning, exact?/apply? (exploration only — prefer explicit lemma names in final proofs).
- You may embed retrieval requests as comments on their own lines inside a block:
    -- LOOGLE: <loogle query>
    -- GREP: <regex over mathlib source>
  The harness executes them and returns results next round."""


def imports_note(imports: list[str]) -> str:
    return "Imports already provided by the harness: " + ", ".join(imports)


def formalize_prompt(problem: dict, k: int, retrieval: list[str], imports: list[str]) -> str:
    ret = "\n".join(retrieval) if retrieval else "(none)"
    return f"""You are the autoformalization stage of a Lean 4 harness for Erdős problems.
{imports_note(imports)}

PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

Context/notes (may inform encoding choices; do NOT weaken the statement):
{problem.get('notes', '(none)')}

Possibly relevant Mathlib declarations:
{ret}

Task: produce {k} INDEPENDENT candidate formalizations of this exact statement.
Each candidate must be a self-contained Lean 4 snippet of the form:

```lean
-- CANDIDATE n
theorem erdos_{problem['id']} <binders/hypotheses> : <goal> := by
  sorry
```

Requirements:
- The theorem statement must capture the problem faithfully — right quantifiers, right domain
  (ℕ vs ℤ vs ℝ), no accidental strengthening or weakening, no trivially-true encodings.
- If the problem asks a yes/no question that is RESOLVED, formalize the resolved assertion
  (e.g. the disproof: the negation of the conjectured statement) and say so in your notes.
- You may add `def`s above the theorem if genuinely needed, but prefer Mathlib vocabulary.
- Vary the encodings across candidates where a real choice exists.
- The name and overall shape must keep `theorem erdos_{problem['id']}` as the theorem being stated.

{HOUSE_RULES}

After the {k} blocks, add a short section titled FAITHFULNESS NOTES explaining, per candidate,
the encoding choices and any risks of mis-capturing the English statement."""


def crosscheck_prompt(problem: dict, candidates: list[str]) -> str:
    listing = "\n\n".join(f"--- CANDIDATE {i} ---\n{c}" for i, c in enumerate(candidates))
    return f"""You are the statement-faithfulness judge of a Lean 4 harness. Be adversarial: your job
is to find any way a candidate formalization FAILS to say exactly what the English problem says.

PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

Notes: {problem.get('notes', '(none)')}

CANDIDATE FORMALIZATIONS (all already compile):
{listing}

For each candidate, hunt for: wrong quantifier order, wrong domain, off-by-one in indices/bounds,
vacuous or trivially-true readings, accidental strengthening/weakening, misencoded "infinitely many",
misencoded density/asymptotics, and resolved-direction errors (proving the conjecture vs its negation).

Then respond with EXACTLY one ```json block:
{{
  "ranking": [<candidate indices, most faithful first>],
  "issues": {{"<index>": "<specific problems, or 'none found'>", ...}},
  "sanity_lean": "<optional: a Lean 4 snippet (no sorry) with `example` checks that instantiate the
                  BEST candidate's statement shape on tiny concrete cases via decide/norm_num, to
                  catch vacuous encodings; empty string if not applicable>"
}}"""


def prove_prompt(problem: dict, statement: str, literature: str, retrieval: list[str],
                 history: str, round_i: int, m: int, imports: list[str]) -> str:
    strategies = [
        "Look hard for an existing Mathlib lemma that is (or nearly is) this statement; the retrieval hits below are a starting point. Glue with simp/norm_num/omega.",
        "Elementary direct argument: unfold definitions, then induction or strong induction with omega/norm_num closing the goals.",
        "Case analysis: split on small cases (interval_cases / decide for finite checks) plus a general argument for the tail.",
        "Contradiction or extremal argument: assume the negation, extract a witness, derive a contradiction with nlinarith/omega and monotonicity lemmas.",
    ]
    strat = strategies[(round_i - 1) % len(strategies)]
    ret = "\n".join(retrieval) if retrieval else "(none)"
    return f"""You are the proof-search stage of a Lean 4 harness (round {round_i}).
{imports_note(imports)}

ENGLISH PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

KNOWN-RESOLUTION CONTEXT (from the literature stage; use it to pick the right proof route):
{literature or '(none)'}

THE THEOREM TO PROVE — its statement is FROZEN. Reproduce it EXACTLY (same name, binders, goal);
you may add `private lemma` helpers ABOVE it in the same block, but must not alter the theorem line(s):
```lean
{statement}
```

Retrieval results:
{ret}

{history}

Primary strategy for this round: {strat}
Produce {m} attempts. Each attempt = one complete file body in its own ```lean block (helpers + the
frozen theorem with a real proof replacing `sorry`). Before each block, write a line `ATTEMPT k: <one-line plan>`.
Make the attempts genuinely different, not cosmetic variations.

{HOUSE_RULES}"""


def decompose_prompt(problem: dict, statement: str, literature: str, history: str,
                     imports: list[str]) -> str:
    return f"""You are the decomposition stage of a Lean 4 harness. Full-proof attempts have failed;
now produce a LEMMA SKELETON: a plan compiled into Lean with `sorry` placeholders.
{imports_note(imports)}

ENGLISH PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

KNOWN-RESOLUTION CONTEXT:
{literature or '(none)'}

FROZEN THEOREM (must appear at the end, proved FROM your helper lemmas — its own proof should be
short glue, not `sorry` if you can manage; the helpers carry the `sorry`s):
```lean
{statement}
```

What failed so far:
{history}

Output EXACTLY one ```lean block: 2-5 helper lemmas (each stated precisely, proof `by sorry`),
then the frozen theorem proved from the helpers. Choose lemmas so each is INDIVIDUALLY provable
by elementary means or a known Mathlib result.

{HOUSE_RULES}"""


def refine_prompt(problem: dict, current: str, errors: list[str], literature: str,
                  retrieval: list[str], imports: list[str]) -> str:
    err = "\n".join(errors) if errors else "(file compiles; sorries remain)"
    ret = "\n".join(retrieval) if retrieval else "(none)"
    return f"""You are the refinement stage of a Lean 4 harness, progressively eliminating `sorry`s.
{imports_note(imports)}

ENGLISH PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

KNOWN-RESOLUTION CONTEXT:
{literature or '(none)'}

CURRENT FILE (compiles except as noted):
```lean
{current}
```

Compiler feedback:
{err}

Retrieval results:
{ret}

Rewrite the file replacing AT LEAST the first remaining `sorry` with a real proof (replace more if
confident). Keep everything else identical, including the final theorem's statement. Output EXACTLY
one ```lean block with the full updated file body.

{HOUSE_RULES}"""


def backtranslate_prompt(statement: str) -> str:
    return f"""Translate this Lean 4 theorem statement into precise plain-English mathematics.
State exactly what is being claimed — quantifiers, domains, bounds. Do not mention Lean or code.
Do not editorialize. 2-5 sentences.

```lean
{statement}
```"""


def compare_prompt(problem: dict, backtranslation: str) -> str:
    return f"""Two mathematical statements follow. Decide whether they assert the same thing.
Be adversarial about quantifier order, domains, edge cases (n=0/1), strict vs non-strict bounds,
and direction (a claim vs its negation).

STATEMENT A (original Erdős problem #{problem['id']}, as resolved):
{problem['statement']}

Resolution notes: {problem.get('notes', '(none)')}

STATEMENT B (independent back-translation of the formalization):
{backtranslation}

Respond with EXACTLY one ```json block: {{"faithful": true|false, "issues": ["..."], "verdict": "<one sentence>"}}
"faithful" means: a proof of B is legitimately a resolution of A (B may be the resolved/negated form of a
disproved conjecture — that counts as faithful if the notes say the problem was resolved that way)."""


def literature_prompt(problem: dict) -> str:
    return f"""You are the literature stage of a Lean 4 harness attempting an Erdős problem.
If you have web access tools, use them; otherwise answer from knowledge, flagging uncertainty.

PROBLEM (erdosproblems.com #{problem['id']}, status: {problem.get('status', 'unknown')}):
{problem['statement']}

Notes: {problem.get('notes', '(none)')}

Report, in plain text:
1. The problem's actual status and who resolved it (with citation if known).
2. The proof/disproof route in enough mathematical detail to guide a formal proof (key lemmas,
   constructions, witnesses — if the resolution is an explicit counterexample, GIVE the witness).
3. Up to 8 Mathlib declarations or concepts likely useful (best-guess names are fine).
4. Pitfalls when formalizing (edge cases, off-by-ones, degenerate cases).
Keep it under 600 words."""


# --------------------------------------------------------------------------- parsing helpers

def lean_blocks(text: str) -> list[str]:
    return [b.strip() for b in re.findall(r"```lean\s*\n(.*?)```", text, re.S)]


def json_block(text: str) -> dict | None:
    m = re.search(r"```json\s*\n(.*?)```", text, re.S)
    if not m:
        return None
    try:
        parsed = json.loads(m.group(1))
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, dict) else None


def strip_imports(src: str) -> str:
    return "\n".join(l for l in src.splitlines() if not l.strip().startswith("import ")).strip()


def norm_ws(s: str) -> str:
    return " ".join(s.split())


def strip_comment_lines(s: str) -> str:
    """Drop whole-line comments (but not inline ones) — they carry no elaboration semantics
    except harness directives, which are handled separately."""
    return "\n".join(l for l in s.splitlines() if not l.strip().startswith("--"))


def extract_directive_imports(body: str) -> list[str]:
    out = []
    for line in re.findall(r"^--\s*IMPORTS?:\s*(.+)$", body, re.M):
        for tok in line.replace(",", " ").split():
            if IMPORT_RE.match(tok):
                out.append(tok)
    return out


def compose(body: str, imports: list[str]) -> str:
    body = strip_imports(body)
    imps = list(dict.fromkeys(imports + extract_directive_imports(body)))
    header = "\n".join(f"import {m}" for m in imps)
    return f"{header}\n\nset_option maxHeartbeats 1000000\n\n{body}\n"


def statement_prefix(statement: str) -> str:
    """Everything up to and including the proof-separating ':=' — the immutable part.
    Candidates are required to end in ':= by sorry', so look for ':= by' specifically;
    a bare first-':=' search would truncate inside let-binders or structure literals."""
    idx = statement.find(":= by")
    if idx == -1:
        idx = statement.rfind(":=")
    if idx == -1:
        raise ValueError("frozen statement has no ':='")
    return statement[: idx + 2]


def contains_frozen(attempt: str, frozen_prefix: str) -> bool:
    return norm_ws(strip_comment_lines(frozen_prefix)) in norm_ws(strip_comment_lines(attempt))


BANNED_RES = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\bsorryAx\b"), "sorryAx"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*axiom\b", re.M), "axiom"),
    (re.compile(r"\bunsafe\b"), "unsafe"),
]


def has_banned(body: str, allow_sorry: bool = False) -> str | None:
    src = strip_comment_lines(body)  # comments can't introduce axioms; avoid '-- axiom of choice' false positives
    for rex, name in BANNED_RES:
        if allow_sorry and name in ("sorry", "sorryAx"):
            continue
        if rex.search(src):
            return name
    return None


# --------------------------------------------------------------------------- the harness

class Harness:
    def __init__(self, args):
        self.problem = json.loads(Path(args.problem).read_text())
        pid = self.problem["id"]
        if args.resume:
            self.run_dir = Path(args.resume).resolve()
        else:
            self.run_dir = RUNS / f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-erdos{pid}"
        self.run_dir.mkdir(parents=True, exist_ok=True)
        cur = RUNS / "current"
        if cur.is_symlink() or cur.exists():
            cur.unlink()
        cur.symlink_to(self.run_dir)
        self.log = RunLog(self.run_dir)
        self.state_path = self.run_dir / "state.json"
        self.state = json.loads(self.state_path.read_text()) if self.state_path.exists() else {}
        self.lean = LeanChecker(FORMAL, args.lean_timeout)
        if args.backend == "claude-cli":
            self.llm = ClaudeCliBackend(args.model, args.llm_timeout)
        else:
            self.llm = FileBackend(self.run_dir, args.llm_timeout)
        self.args = args
        self.checks = 0
        self.imports = self.problem.get("imports", DEFAULT_IMPORTS)
        self._lock = threading.Lock()

    # -- infrastructure

    def save(self):
        self.state_path.write_text(json.dumps(self.state, indent=2))

    def check(self, body: str, name: str) -> dict:
        with self._lock:
            self.checks += 1
        src = compose(body, self.imports)
        res = self.lean.check(src, self.run_dir / "attempts" / f"{name}.lean")
        self.log.event("lean", "check", name=name, ok=res["ok"], sorries=res["sorries"],
                       n_errors=len(res["errors"]), first_error=(res["errors"][0] if res["errors"] else ""))
        return res

    def ask(self, purpose: str, prompt: str) -> str:
        self.log.event("llm", "request", purpose=purpose, chars=len(prompt))
        t0 = time.time()
        text = self.llm.complete(purpose, prompt)
        self.log.event("llm", "response", purpose=purpose, chars=len(text), secs=round(time.time() - t0, 1))
        (self.run_dir / "transcripts").mkdir(exist_ok=True)
        n = len(list((self.run_dir / "transcripts").glob("*.md"))) + 1
        (self.run_dir / "transcripts" / f"{n:03d}-{purpose}.md").write_text(
            f"# {purpose}\n\n## prompt\n\n{prompt}\n\n## response\n\n{text}\n")
        return text

    # -- stages

    def stage_literature(self):
        if self.args.skip_literature:
            self.state["literature"] = ""
            return
        if "literature" in self.state:
            return
        self.state["literature"] = self.ask("literature", literature_prompt(self.problem)).strip()
        self.save()

    def initial_retrieval(self) -> list[str]:
        hits = grep_mathlib(r"theorem .*[Ee]rdos", 10)
        words = re.findall(r"[A-Za-z]{5,}", self.problem["statement"])[:4]
        for w in words:
            hits += loogle(f'"{w.lower()}"', 4)
        return hits[:20]

    def stage_formalize(self):
        if "statement" in self.state:
            return
        retrieval = self.initial_retrieval()
        candidates, notes = [], ""
        for attempt in range(1, 4):  # up to 3 tries to get >=2 compiling candidates
            resp = self.ask("formalize", formalize_prompt(self.problem, self.args.samples + 1,
                                                          retrieval, self.imports))
            notes = resp
            blocks = [(i, "\n".join(l for l in b.splitlines()
                                    if not l.strip().lower().startswith("-- candidate")).strip())
                      for i, b in enumerate(lean_blocks(resp))]
            blocks = [(i, b) for i, b in blocks if f"erdos_{self.problem['id']}" in b]
            with ThreadPoolExecutor(max_workers=COMPILE_WORKERS) as ex:
                results = list(ex.map(lambda t: self.check(t[1], f"cand-{attempt}-{t[0]}"), blocks))
            for (i, block), res in zip(blocks, results):
                if res["ok"] and res["sorries"]:
                    candidates.append(block)
            if len(candidates) >= 2:
                break
            retrieval = retrieval[:10]
        if not candidates:
            raise SystemExit("formalize: no candidate statement compiled — aborting")
        self.log.event("formalize", "candidates_compiled", n=len(candidates))

        cc = self.ask("crosscheck", crosscheck_prompt(self.problem, candidates))
        verdict = json_block(cc) or {"ranking": list(range(len(candidates))), "issues": {}}
        order = [i for i in verdict.get("ranking", []) if isinstance(i, int) and 0 <= i < len(candidates)]
        order += [i for i in range(len(candidates)) if i not in order]
        chosen = candidates[order[0]]

        sanity = (verdict.get("sanity_lean") or "").strip()
        if sanity:
            res = self.check(chosen + "\n\n" + sanity, "sanity")
            self.log.event("formalize", "sanity", ok=res["ok"],
                           detail=(res["errors"][0] if res["errors"] else "passed"))
            if not res["ok"] and len(order) > 1:
                self.log.event("formalize", "sanity_failed_trying_next", idx=order[1])
                chosen = candidates[order[1]]

        self.state["statement"] = chosen
        self.state["crosscheck"] = verdict
        self.state["formalize_notes"] = notes[-3000:]
        self.save()
        self.log.event("formalize", "frozen", statement=chosen)

    def _history_digest(self, attempts: list[dict], cap: int = 8) -> str:
        if not attempts:
            return "No prior attempts."
        lines = ["WHAT FAILED SO FAR (do not repeat these exact failures):"]
        for a in attempts[-cap:]:
            errs = "; ".join(a["errors"][:2]) or ("timed out" if a.get("timeout") else "left sorries")
            lines.append(f"- {a['name']} [{a['plan'][:100]}]: {errs[:500]}")
        return "\n".join(lines)

    def stage_prove(self) -> bool:
        if self.state.get("proof"):
            return True
        statement = self.state["statement"]
        frozen = statement_prefix(statement)
        attempts = self.state.get("attempts", [])
        retrieval = self.initial_retrieval()
        for rnd in range(1, self.args.rounds + 1):
            resp = self.ask("prove", prove_prompt(
                self.problem, statement, self.state.get("literature", ""),
                retrieval, self._history_digest(attempts), rnd, self.args.samples, self.imports))
            plans = re.findall(r"^ATTEMPT\s+\d+:\s*(.+)$", resp, re.M)
            blocks = lean_blocks(resp)
            retrieval = run_retrieval_directives(resp) or retrieval
            # cheap pre-screen, then compile survivors in parallel
            to_compile = []
            for i, block in enumerate(blocks):
                name = f"proof-r{rnd}-a{i}"
                plan = plans[i] if i < len(plans) else "?"
                if not contains_frozen(block, frozen):
                    attempts.append({"name": name, "plan": plan, "errors": ["attempt altered the frozen theorem statement — rejected without compiling"]})
                    self.log.event("prove", "frozen_violation", name=name)
                    continue
                banned = has_banned(block)
                if banned:
                    attempts.append({"name": name, "plan": plan, "errors": [f"used banned construct `{banned}` — rejected"]})
                    self.log.event("prove", "banned", name=name, construct=banned)
                    continue
                to_compile.append((i, name, plan, block))
            if to_compile:
                with ThreadPoolExecutor(max_workers=COMPILE_WORKERS) as ex:
                    results = list(ex.map(lambda t: self.check(t[3], t[1]), to_compile))
                for (i, name, plan, block), res in zip(to_compile, results):
                    if res["ok"] and not res["sorries"] and "proof" not in self.state:
                        self.state["proof"] = block
                        self.state["attempts"] = attempts
                        self.save()
                        self.log.event("prove", "SUCCESS", name=name, round=rnd)
                        return True
                    if not (res["ok"] and not res["sorries"]):
                        attempts.append({"name": name, "plan": plan, "errors": res["errors"][:4],
                                         "timeout": res.get("timeout", False)})
                        # feed Try-this suggestions from exact?/apply? into next round's retrieval
                        tries = [x for x in res["infos"] if "Try this" in x]
                        if tries:
                            retrieval = (retrieval + [f"suggestion from {name}: {t}" for t in tries])[-20:]
            self.state["attempts"] = attempts
            self.save()
        return False

    def stage_decompose(self) -> bool:
        statement = self.state["statement"]
        frozen = statement_prefix(statement)
        history = self._history_digest(self.state.get("attempts", []))
        skeleton = None
        for attempt in range(1, 4):
            resp = self.ask("decompose", decompose_prompt(
                self.problem, statement, self.state.get("literature", ""), history, self.imports))
            blocks = lean_blocks(resp)
            if not blocks:
                continue
            block = max(blocks, key=len)
            if not contains_frozen(block, frozen):
                history += f"\n- decompose attempt {attempt}: altered the frozen theorem — rejected."
                continue
            res = self.check(block, f"skeleton-{attempt}")
            if res["ok"]:  # sorries allowed here
                skeleton = block
                break
            history += f"\n- skeleton attempt {attempt} failed: {'; '.join(res['errors'][:2])[:400]}"
        if not skeleton:
            self.log.event("decompose", "no_valid_skeleton")
            return False
        self.log.event("decompose", "skeleton_accepted", sorries=skeleton.count("sorry"))

        current = skeleton
        budget = self.args.decompose_rounds
        retrieval: list[str] = []
        last_errors: list[str] = []
        while budget > 0 and "sorry" in current:
            budget -= 1
            resp = self.ask("refine", refine_prompt(self.problem, current, last_errors,
                                                    self.state.get("literature", ""), retrieval,
                                                    self.imports))
            blocks = lean_blocks(resp)
            retrieval = run_retrieval_directives(resp) or retrieval
            if not blocks:
                last_errors = ["(no lean block in response)"]
                continue
            cand = max(blocks, key=len)
            if not contains_frozen(cand, frozen):
                last_errors = ["refinement altered the frozen theorem statement — rejected"]
                continue
            res = self.check(cand, f"refine-{self.args.decompose_rounds - budget}")
            if res["ok"] and cand.count("sorry") < current.count("sorry"):
                current = cand
                last_errors = []
                self.log.event("decompose", "progress", sorries_left=cand.count("sorry"))
            elif res["ok"]:
                last_errors = [f"no progress: still {cand.count('sorry')} sorries"]
            else:
                last_errors = res["errors"][:4]
        if "sorry" not in current and not has_banned(current):
            final = self.check(current, "assembled")
            if final["ok"] and not final["sorries"]:
                self.state["proof"] = current
                self.save()
                self.log.event("decompose", "SUCCESS")
                return True
        return False

    def stage_verify(self) -> dict:
        proof = self.state["proof"]
        thm = f"erdos_{self.problem['id']}"
        res = self.check(proof + f"\n\n#print axioms {thm}\n", "final-verify")
        # `#print axioms` output may lack a file:line prefix, so scan the raw output.
        m = re.search(rf"'{re.escape(thm)}' depends on axioms:\s*\[([^\]]*)\]", res["raw"])
        if m:
            axline = m.group(0)
            axioms = {t.strip() for t in m.group(1).split(",") if t.strip()}
        elif re.search(rf"'{re.escape(thm)}' does not depend on any axioms", res["raw"]):
            axline = f"'{thm}' does not depend on any axioms"
            axioms = set()
        else:
            axline, axioms = "", {"UNKNOWN(#print axioms output not found)"}
        clean = res["ok"] and not res["sorries"] and axioms <= STD_AXIOMS and bool(axline)

        back = self.ask("backtranslate", backtranslate_prompt(self.state["statement"])).strip()
        cmp_resp = self.ask("faithful", compare_prompt(self.problem, back))
        faithful = json_block(cmp_resp) or {"faithful": None, "issues": ["judge returned no JSON"]}

        verdict = {
            "compiles": res["ok"], "sorry_free": not res["sorries"],
            "axioms": sorted(axioms), "axioms_clean": axioms <= STD_AXIOMS,
            "backtranslation": back, "faithful": faithful, "all_clear": clean and bool(faithful.get("faithful")),
        }
        self.state["verify"] = verdict
        self.save()
        self.log.event("verify", "done", **{k: v for k, v in verdict.items() if k != "backtranslation"})
        if clean:
            out = self.run_dir / "final" / f"Erdos{self.problem['id']}.lean"
            out.parent.mkdir(exist_ok=True)
            out.write_text(compose(proof, self.imports))
        return verdict

    def report(self, proved: bool):
        v = self.state.get("verify", {})
        # derive counts from the event log so they survive --resume across processes
        try:
            events = [json.loads(l) for l in open(self.log.path)]
        except Exception:
            events = []
        n_checks = sum(1 for e in events if e.get("event") == "check") or self.checks
        rejected = sum(1 for e in events if e.get("stage") == "prove"
                       and e.get("event") in ("frozen_violation", "banned"))
        compiled = sum(1 for e in events if e.get("event") == "check"
                       and str(e.get("name", "")).startswith(("proof-", "refine-", "skeleton")))
        n_attempts = rejected + compiled
        lines = [
            f"# Harness run report — Erdős problem #{self.problem['id']}",
            "",
            f"- **Status:** {'PROVED & VERIFIED' if proved and v.get('all_clear') else 'PROVED (verification caveats — see below)' if proved else 'NOT PROVED (out of budget)'}",
            f"- **Problem:** {self.problem['statement']}",
            f"- **Source:** {self.problem.get('url', '')}",
            f"- **Lean checks run:** {n_checks}; proof attempts: {n_attempts}",
            "",
            "## Frozen formal statement",
            "```lean", self.state.get("statement", "(none)"), "```",
            "",
        ]
        if proved:
            lines += [
                "## Verification",
                f"- compiles: {v.get('compiles')}  |  sorry-free: {v.get('sorry_free')}  |  axioms: {v.get('axioms')} (clean: {v.get('axioms_clean')})",
                f"- faithfulness (blind back-translation judge): {v.get('faithful')}",
                "",
                "### Blind back-translation of the formal statement",
                v.get("backtranslation", ""),
                "",
                "## Final proof",
                "```lean", self.state.get("proof", ""), "```",
            ]
        else:
            lines += ["## Last attempt digest", self._history_digest(self.state.get("attempts", []), cap=12)]
        (self.run_dir / "report.md").write_text("\n".join(lines) + "\n")

    def run(self):
        pid = self.problem["id"]
        self.log.event("run", "start", problem=pid, backend=self.args.backend,
                       resume=bool(self.args.resume))
        try:
            self.stage_literature()
            self.stage_formalize()
            proved = self.stage_prove()
            if not proved:
                self.log.event("run", "escalating_to_decompose")
                proved = self.stage_decompose()
            if proved:
                self.stage_verify()
            self.report(proved)
            self.log.event("run", "end", proved=proved,
                           all_clear=self.state.get("verify", {}).get("all_clear"))
            (self.run_dir / "DONE").write_text(json.dumps(
                {"proved": proved, "verify": self.state.get("verify", {}).get("all_clear")}))
            return 0 if proved else 2
        except BaseException as e:
            self.log.event("run", "fatal", error=repr(e)[:500])
            (self.run_dir / "DONE").write_text(json.dumps({"proved": False, "fatal": repr(e)[:200]}))
            raise


def main():
    ap = argparse.ArgumentParser(description="LLM + Lean 4 harness for Erdős problems")
    sub = ap.add_subparsers(dest="cmd", required=True)

    runp = sub.add_parser("run")
    runp.add_argument("--problem", required=True)
    runp.add_argument("--backend", choices=["claude-cli", "file"], default="claude-cli")
    runp.add_argument("--model", default=None, help="model for claude-cli backend")
    runp.add_argument("--samples", type=int, default=3, help="attempts requested per proving round")
    runp.add_argument("--rounds", type=int, default=6, help="max proving rounds before decomposition")
    runp.add_argument("--decompose-rounds", type=int, default=10, help="refinement budget after decomposition")
    runp.add_argument("--skip-literature", action="store_true")
    runp.add_argument("--resume", default=None, help="existing run dir to resume")
    runp.add_argument("--lean-timeout", type=int, default=420)
    runp.add_argument("--llm-timeout", type=int, default=1800)

    chk = sub.add_parser("check")
    chk.add_argument("file")
    chk.add_argument("--lean-timeout", type=int, default=420)

    args = ap.parse_args()
    if args.cmd == "check":
        checker = LeanChecker(FORMAL, args.lean_timeout)
        res = checker.check(Path(args.file).read_text(), RUNS / "adhoc" / Path(args.file).name)
        print(json.dumps(res, indent=2))
        return 0 if res["ok"] else 1
    return Harness(args).run()


if __name__ == "__main__":
    sys.exit(main())
