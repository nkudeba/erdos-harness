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
from solution_review import milestones, fingerprint, environment_snapshot, load_attestations
from result_feed import export_run, atomic as feed_atomic
import hashlib
import uuid
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import tempfile
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
# Import header economics (measured on a 16GB M-series laptop, Mathlib v4.32.0-rc1):
#   full `import Mathlib`            ~200 s / check, ~3 GB
#   `import Mathlib.Tactic` bundle   ~47 s / check, ~1.7 GB   <- default: every tactic the prompts mention exists
#   three hand-picked tactic files   ~20 s / check              <- old default; `positivity`, `interval_cases`,
#                                                                  `field_simp`, `gcongr`, `decide +kernel` etc. were MISSING
# Problems can override via an "imports" field; models can request more via `-- IMPORTS:`; and the
# harness auto-resolves `unknown identifier` errors to the Mathlib module that defines the name.
DEFAULT_IMPORTS = [
    "Mathlib.Tactic",
    "Mathlib.Algebra.BigOperators.Fin",
    "Mathlib.Data.Nat.Factorial.Basic",
    "Mathlib.Data.Nat.Prime.Basic",
]
IMPORT_RE = re.compile(r"^Mathlib(\.[A-Za-z0-9'!?]+)+$")
BANNED_IN_PROOFS = ["sorry", "admit", "native_decide", "\naxiom ", "unsafe ", "sorryAx"]
COMPILE_WORKERS = int(os.environ.get("ERDOS_COMPILE_WORKERS", "3"))
MATHLIB_SRC = FORMAL / ".lake" / "packages" / "mathlib" / "Mathlib"
KNOWLEDGE = Path(os.environ.get("ERDOS_KNOWLEDGE", str(ROOT / "knowledge"))).resolve()


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
    """Production backend: `claude -p` in print mode with a scrubbed environment.

    Two call shapes:
      * complete()         — one-shot, no tools: the model writes text, the harness compiles it.
      * complete_agentic() — the model works inside a sandbox directory with a scoped tool set
                             (edit files + run `./check.sh` = `lake env lean`), so it gets compiler
                             feedback within its own turn. The harness STILL independently compiles
                             and verifies whatever it returns — the sandbox is a scratchpad, not a proof.
    Every call is JSON-mode so cost/turns/duration are captured and logged.
    """

    # Effort/budget per call purpose. Measured on #363: the literature summary cost $6.52 (25 min of thinking)
    # at the default effort; medium effort is plenty for retrieval-style stages. Proof search keeps the default.
    AUX_PURPOSES = {"literature", "backtranslate", "faithful", "retrospect"}
    FORMAL_PURPOSES = {"formalize", "crosscheck"}
    TRIAGE_PURPOSES = {"assess", "critic", "search"}   # medium effort, $1 cap: classification / review / script writing

    def __init__(self, model: str | None, timeout: int, call_budget_usd: float = 8.0,
                 aux_effort: str | None = "medium", formal_effort: str | None = "high",
                 prove_effort: str | None = None, aux_budget_usd: float = 2.5, formal_budget_usd: float = 4.0):
        self.model = model
        self.timeout = timeout
        self.call_budget_usd = call_budget_usd
        self.aux_effort, self.formal_effort, self.prove_effort = aux_effort, formal_effort, prove_effort
        self.aux_budget_usd, self.formal_budget_usd = aux_budget_usd, formal_budget_usd
        self.bin = shutil.which("claude") or f"{os.environ['HOME']}/.local/bin/claude"
        self.total_cost_usd = 0.0
        self.total_tokens: dict = {"in": 0, "out": 0, "cache_read": 0, "cache_write": 0}
        self.calls = 0
        self.last_meta: dict = {}
        self._lock = threading.Lock()

    # Transient provider/network failures are retried with backoff; anything else (usage limit reached, budget
    # exceeded, auth) propagates as RuntimeError so the run stops as an infrastructure failure (resumable).
    TRANSIENT_RE = re.compile(r"reach the API|ENOTFOUND|ECONNRESET|ETIMEDOUT|ECONNREFUSED|overloaded|Overloaded|"
                              r"\b(?:502|503|504|529)\b|rate limit|Rate limit|temporarily unavailable|internal server error|"
                              r"[Rr]equest timed out|timed out|connection error",
                              re.I)
    RETRIES = 3
    BACKOFF_S = (45, 90, 180)
    # Hard failures: never retried, never treated as a failed proof attempt — the run stops (resumable).
    HARD_RE = re.compile(r"spend limit|usage limit|hit your (?:org's )?(?:monthly|weekly|daily)?\s*(?:spend|usage)|"
                         r"usage-credits|not logged in|unauthori[sz]ed|invalid api key|authentication", re.I)

    def _tuning(self, purpose: str) -> tuple[str | None, float]:
        if purpose in self.TRIAGE_PURPOSES:
            return "medium", 1.0
        if purpose in self.AUX_PURPOSES:
            return self.aux_effort, self.aux_budget_usd
        if purpose in self.FORMAL_PURPOSES:
            return self.formal_effort, self.formal_budget_usd
        return self.prove_effort, self.call_budget_usd

    def _run(self, purpose: str, prompt: str, extra: list[str], cwd: Path | None,
             effort_override: str | None = None, budget_override: float | None = None) -> str:
        effort, budget = self._tuning(purpose)
        if effort_override:
            effort = effort_override
        if budget_override:
            budget = budget_override
        cmd = [self.bin, "-p", "--output-format", "json", "--max-budget-usd", str(budget)] + extra
        if effort:
            cmd += ["--effort", effort]
        if self.model:
            cmd += ["--model", self.model]
        last_err = ""
        for attempt in range(self.RETRIES + 1):
            try:
                r = subprocess.run(cmd, input=prompt, capture_output=True, text=True,
                                   timeout=self.timeout, env=clean_env(), cwd=str(cwd) if cwd else None)
            except subprocess.TimeoutExpired:
                # a hung/slow provider call: retry once more if budget allows, else surface as RuntimeError
                last_err = f"timeout after {self.timeout}s"
                if attempt < self.RETRIES:
                    print(f"[{now()}] backend/retry purpose={purpose} attempt={attempt + 1}/{self.RETRIES}: {last_err}",
                          file=sys.stderr, flush=True)
                    continue
                break
            try:
                d = json.loads(r.stdout)
                text = d.get("result") or ""
                mu = d.get("modelUsage") or {}
                tokens = {"in": sum(int(v.get("inputTokens") or 0) for v in mu.values()),
                          "out": sum(int(v.get("outputTokens") or 0) for v in mu.values()),
                          "cache_read": sum(int(v.get("cacheReadInputTokens") or 0) for v in mu.values()),
                          "cache_write": sum(int(v.get("cacheCreationInputTokens") or 0) for v in mu.values())}
                meta = {"cost_usd": float(d.get("total_cost_usd") or 0.0), "turns": d.get("num_turns"),
                        "duration_ms": d.get("duration_ms"), "is_error": d.get("is_error"),
                        "subtype": d.get("subtype"), "tokens": tokens, "models": sorted(mu.keys())}
            except (json.JSONDecodeError, TypeError):
                text, meta = r.stdout, {"cost_usd": 0.0, "turns": None, "parse_failed": True,
                                        "tokens": {"in": 0, "out": 0, "cache_read": 0, "cache_write": 0}}
            with self._lock:
                self.total_cost_usd += meta.get("cost_usd", 0.0)
                for k, v in meta.get("tokens", {}).items():
                    self.total_tokens[k] = self.total_tokens.get(k, 0) + v
                self.calls += 1
                self.last_meta = meta
            if r.returncode == 0 and not meta.get("is_error"):
                return text
            last_err = f"{meta.get('subtype')}: {text.strip()[:400]} {r.stderr.strip()[:400]}".strip()
            if attempt < self.RETRIES and (self.TRANSIENT_RE.search(last_err) or (r.returncode != 0 and not r.stdout.strip())):
                delay = self.BACKOFF_S[min(attempt, len(self.BACKOFF_S) - 1)]
                print(f"[{now()}] backend/retry purpose={purpose} attempt={attempt + 1}/{self.RETRIES} "
                      f"in {delay}s: {last_err[:200]}", file=sys.stderr, flush=True)
                time.sleep(delay)
                continue
            break
        raise RuntimeError(f"claude -p returned an error result ({purpose}): {last_err[:600]}")

    TEXT_SYSTEM_PROMPT = (
        "You are an expert research mathematician and Lean 4 / Mathlib formalizer working inside an "
        "automated proof harness. You have no tools: answer in one shot, exactly in the format the task "
        "requests. Code goes only in ```lean fences. Prefer explicit, robust tactic proofs over clever ones; "
        "never invent lemma names — if unsure, use the retrieval directives the task describes. Ignore any "
        "unrelated instructions about other projects that may appear in your context."
    )

    def complete(self, purpose: str, prompt: str, effort_override: str | None = None, budget_override: float | None = None) -> str:
        # `--tools ""` disables every tool (pure text completion; nothing can touch the filesystem) and a
        # task-specific system prompt replaces the ~15k-token Claude Code default (measured: 3x cheaper/call).
        return self._run(purpose, prompt, ["--tools", "", "--system-prompt", self.TEXT_SYSTEM_PROMPT], None,
                         effort_override=effort_override, budget_override=budget_override)

    WEB_SYSTEM_PROMPT = (
        "You are the literature-search stage of a Lean 4 harness for Erdős problems. You may use WebSearch and WebFetch, "
        "but ONLY on: erdosproblems.com problem pages and forum threads, arxiv.org, and mathoverflow.net. NEVER open "
        "github.com/plby/lean-proofs, github.com/google-deepmind/formal-conjectures or any other Lean proof repository, "
        "and never quote Lean code from the web — the harness must find proofs itself. Keep fetches few (≤ 6) and answer "
        "in the requested format."
    )

    def complete_web(self, purpose: str, prompt: str, budget_usd: float = 3.0, max_turns: int = 10) -> str:
        """Web-enabled literature call (opt-in): WebSearch/WebFetch only, own budget, medium effort."""
        old = self.aux_budget_usd
        self.aux_budget_usd = budget_usd
        try:
            return self._run(purpose, prompt, ["--tools", "WebSearch", "WebFetch", "--allowedTools", "WebSearch", "WebFetch",
                                               "--max-turns", str(max_turns), "--system-prompt", self.WEB_SYSTEM_PROMPT], None)
        finally:
            self.aux_budget_usd = old

    def complete_agentic(self, purpose: str, prompt: str, sandbox: Path, max_turns: int) -> str:
        """Tool-enabled call confined to `sandbox`: file edits auto-accepted only there, the sole
        shell command allowed is `./check.sh` (which runs the Lean checker), reads may reach the
        Mathlib sources for grepping."""
        extra = ["--max-turns", str(max_turns), "--permission-mode", "acceptEdits",
                 "--allowedTools", "Bash(./check.sh:*)", "Read", "Edit", "Write", "Grep", "Glob",
                 "--add-dir", str(FORMAL)]
        return self._run(purpose, prompt, extra, sandbox)


class CodexCliBackend:
    """Alternate CLI provider; final text is captured separately from progress output."""

    def __init__(self, model=None, timeout=3600):
        self.model, self.timeout = model, timeout
        self.last_meta = {}
        self.bin = shutil.which("codex")
        if not self.bin:
            raise RuntimeError("codex CLI is not installed")

    def complete(self, purpose, prompt):
        with tempfile.TemporaryDirectory(prefix="erdos-codex-") as tmp:
            out = Path(tmp) / "response.txt"
            cmd = [self.bin, "exec", "--ignore-user-config", "--ephemeral",
                   "--skip-git-repo-check", "--sandbox", "read-only", "--color", "never",
                   "-c", 'model_reasoning_effort="high"', "-o", str(out), "-"]
            if self.model:
                cmd += ["--model", self.model]
            result = subprocess.run(cmd, input="Answer the following proof-harness request in text only. "
                                    "Do not use tools or read local files.\n\n" + prompt,
                                    capture_output=True, text=True, timeout=self.timeout, cwd=tmp)
            self.last_meta = {"provider": "codex-cli", "cost_usd": None}
            if result.returncode != 0 or not out.exists() or not out.read_text().strip():
                raise RuntimeError(f"codex failed ({purpose}): {result.stderr[-1000:]}")
            return out.read_text()

    def complete_agentic(self, purpose, prompt, sandbox, max_turns):
        # Codex has no max-turns option; the subprocess timeout bounds this session.
        with tempfile.TemporaryDirectory(prefix="erdos-codex-agent-") as tmp:
            out = Path(tmp) / "response.txt"
            cmd = [self.bin, "exec", "--ignore-user-config", "--ephemeral",
                   "--skip-git-repo-check", "--sandbox", "workspace-write", "--color", "never",
                   "-C", str(sandbox), "-c", 'model_reasoning_effort="high"', "-o", str(out), "-"]
            if self.model:
                cmd += ["--model", self.model]
            result = subprocess.run(cmd, input=prompt, capture_output=True, text=True,
                                    timeout=self.timeout, cwd=sandbox)
            (sandbox / "provider.log").write_text(result.stdout + "\n" + result.stderr)
            self.last_meta = {"provider": "codex-cli", "cost_usd": None}
            if result.returncode != 0 or not out.exists():
                raise RuntimeError(f"codex agent failed ({purpose}): {result.stderr[-1000:]}")
            return out.read_text()


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
    # Lean ≥ 4.2x tags diagnostics with a code: `path:8:23: error(lean.unknownIdentifier): Unknown identifier ...`.
    # The original pattern required a bare `error:` and therefore DROPPED every coded message (unknown identifiers,
    # invalid fields, ...) from the feedback shown to the prover. The optional `(...)` group fixes that.
    MSG_RE = re.compile(r"^(?P<path>[^\s:][^:\n]*):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info)(?:\((?P<code>[^)]*)\))?: ?(?P<msg>.*)$")

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
        # Goal states are the most useful part of an error for repair — keep them long.
        def fmt(m, cap):
            cap = 1800 if ("unsolved goals" in m["msg"] or "⊢" in m["msg"]) else cap
            return f"line {m['line']}:{m['col']}: {m['msg'][:cap]}"
        return {
            "ok": r.returncode == 0 and not errors,
            "timeout": False,
            "errors": [fmt(m, 700) for m in errors],
            "warnings": [fmt(m, 300) for m in warnings],
            "infos": [fmt(m, 600) for m in infos],
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
        rg = shutil.which("rg")
        cmd = [rg, "-n", "--glob", "*.lean", "--", pattern, str(src)] if rg else ["grep", "-rInE", "--include=*.lean", pattern, str(src)]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=60, env=clean_env())
        lines = [l.replace(str(src), "Mathlib") for l in r.stdout.splitlines()]
        return lines[:limit]
    except Exception:
        return []


def merge_retrieval(previous: list[str], fresh: list[str], max_chars: int = 48000) -> list[str]:
    """Keep recent distinct evidence across stages, with a bounded prompt footprint."""
    unique = list(dict.fromkeys(previous + fresh))
    kept, size = [], 0
    for item in reversed(unique):
        item = item[:24000]
        if size + len(item) <= max_chars:
            kept.append(item)
            size += len(item)
    return list(reversed(kept))


def run_retrieval_directives(text: str) -> list[str]:
    """Attempts may embed `-- LOOGLE: <q>` / `-- GREP: <regex>` / `-- CHECK: Name.of.decl` comments; execute them."""
    out = []
    for q in re.findall(r"^--\s*LOOGLE:\s*(.+)$", text, re.M)[:4]:
        hits = loogle(q.strip())
        out.append(f"loogle `{q.strip()}`:\n  " + ("\n  ".join(hits) if hits else "(no hits)"))
    for q in re.findall(r"^--\s*GREP:\s*(.+)$", text, re.M)[:4]:
        hits = grep_mathlib(q.strip())
        out.append(f"grep `{q.strip()}`:\n  " + ("\n  ".join(hits) if hits else "(no hits)"))
    for module in re.findall(r"^--\s*READ:\s*(\S+)", text, re.M)[:2]:
        if IMPORT_RE.fullmatch(module):
            path = MATHLIB_SRC.parent.joinpath(*module.split(".")).with_suffix(".lean")
            if path.is_file():
                source = path.read_text()
                out.append(f"SOURCE {module} (first 24000 characters):\n" + source[:24000])
    names = []
    for line in re.findall(r"^--\s*CHECK:\s*(.+)$", text, re.M)[:4]:
        names += [t for t in re.split(r"[,\s]+", line.strip()) if t]
    if names:
        out.append(verify_names(names[:12]))
    return out


# ---- declaration lookup: the antidote to hallucinated lemma names -------------------------------

DECL_KINDS = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)"
_decl_cache: dict[str, tuple[str, str] | None] = {}


def module_of_path(path: str) -> str:
    rel = os.path.relpath(path, MATHLIB_SRC.parent)
    return rel[:-5].replace(os.sep, ".") if rel.endswith(".lean") else rel.replace(os.sep, ".")


class DeclIndex:
    """One-pass index of every declaration in Mathlib + Batteries + Lean core (`Init`), keyed by fully
    qualified name, with `namespace` tracking and synthesized `to_additive` twins. Built once (~20-40 s),
    cached on disk keyed by the Mathlib revision; lookups are then instant and support fuzzy suggestions.
    """
    DECL_RE = re.compile(
        rf"^(?P<attr>(?:@\[[^\]]*\]\s*)*)(?:(?:protected|private|noncomputable|nonrec|scoped|partial|unsafe)\s+)*"
        rf"(?P<kind>{DECL_KINDS})\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.!?]*)")
    ADD_MAP = [("prod", "sum"), ("Prod", "Sum"), ("mul", "add"), ("Mul", "Add"), ("one", "zero"), ("One", "Zero"),
               ("inv", "neg"), ("Inv", "Neg"), ("div", "sub"), ("Div", "Sub"), ("pow", "nsmul"), ("npow", "nsmul"),
               ("zpow", "zsmul"), ("Monoid", "AddMonoid"), ("Group", "AddGroup"), ("monoid", "addMonoid"),
               ("Comm", "AddComm")]

    def __init__(self):
        self.by_name: dict[str, tuple[str, str, str]] = {}   # fq name -> (module, kind, signature)
        self.by_last: dict[str, list[str]] = {}
        self.ready = False

    @staticmethod
    def _roots() -> list[tuple[Path, str]]:
        roots = [(MATHLIB_SRC, "Mathlib")]
        bat = FORMAL / ".lake" / "packages" / "batteries" / "Batteries"
        if bat.exists():
            roots.append((bat, "Batteries"))
        tc = FORMAL / "lean-toolchain"
        try:
            name = tc.read_text().strip().replace("/", "--").replace(":", "---")
            core = Path.home() / ".elan" / "toolchains" / name / "src" / "lean" / "Init"
            if core.exists():
                roots.append((core, "Init"))
        except OSError:
            pass
        return roots

    def _cache_path(self) -> Path:
        rev = "unknown"
        try:
            man = json.loads((FORMAL / "lake-manifest.json").read_text())
            for p in man.get("packages", []):
                if p.get("name") == "mathlib":
                    rev = (p.get("rev") or p.get("inputRev") or "unknown")[:12]
        except Exception:
            pass
        d = ROOT / "runs" / ".cache"
        d.mkdir(parents=True, exist_ok=True)
        return d / f"decl_index-{rev}.tsv"

    def build(self, log=None):
        cache = self._cache_path()
        if cache.exists():
            for line in cache.read_text().splitlines():
                parts = line.split("\t")
                if len(parts) == 4:
                    self._add(parts[0], parts[1], parts[2], parts[3])
            self.ready = bool(self.by_name)
            if self.ready:
                return
        t0 = time.time()
        for root, top in self._roots():
            for path in root.rglob("*.lean"):
                try:
                    self._scan_file(path, root, top)
                except Exception:
                    continue
        with open(cache, "w") as f:
            for n, (mod, kind, sig) in self.by_name.items():
                f.write(f"{n}\t{mod}\t{kind}\t{sig}\n")
        self.ready = True
        if log:
            log.event("index", "built", decls=len(self.by_name), secs=round(time.time() - t0, 1))

    def _add(self, name, mod, kind, sig):
        if name not in self.by_name:
            self.by_name[name] = (mod, kind, sig)
            self.by_last.setdefault(name.split(".")[-1], []).append(name)

    def _additive(self, name: str) -> str:
        out = name
        for a, b in self.ADD_MAP:
            out = re.sub(rf"(?<![A-Za-z]){a}(?![a-z])", b, out) if a[0].isupper() else re.sub(rf"(?<![a-zA-Z]){a}(?![a-zA-Z])", b, out)
        return out

    def _scan_file(self, path: Path, root: Path, top: str):
        rel = path.relative_to(root).with_suffix("")
        mod = ".".join((top,) + rel.parts)
        ns: list[str] = []
        lines = path.read_text(errors="replace").splitlines()
        pending_attr = ""
        i = 0
        while i < len(lines):
            line = lines[i]
            s = line.strip()
            m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", s)
            if m:
                ns.append(m.group(1)); i += 1; continue
            m = re.match(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$", s)
            if m and m.group(1) and ns and ns[-1] == m.group(1):
                ns.pop(); i += 1; continue
            if s.startswith("@[") and not re.search(rf"\b{DECL_KINDS}\b", s):
                pending_attr += " " + s; i += 1; continue   # attribute on its own line(s)
            m = self.DECL_RE.match(line) if not line.startswith((" ", "\t")) else None
            if m:
                attr = (pending_attr + " " + m.group("attr")).strip()
                pending_attr = ""
                name = m.group("name")
                fq = name if name.startswith("_root_.") else ".".join(ns + [name]) if ns else name
                fq = fq.replace("_root_.", "")
                sig = []
                for j in range(i, min(i + 5, len(lines))):
                    sig.append(lines[j].strip())
                    if ":=" in lines[j] or lines[j].rstrip().endswith("where") or "|" == lines[j].strip()[:1]:
                        break
                sigtext = " ".join(sig)
                sigtext = re.sub(r"^(?:@\[[^\]]*\]\s*)*", "", sigtext).split(":=")[0].strip()[:400]
                self._add(fq, mod, m.group("kind"), sigtext)
                ta = re.search(r"to_additive(?:\s+(?:\([^)]*\)\s*)?(?:\"[^\"]*\"\s*)?)?([A-Za-z_][A-Za-z0-9_'.]*)?", attr)
                if "to_additive" in attr:
                    add_name = ta.group(1) if (ta and ta.group(1) and ta.group(1) not in ("existing",)) else None
                    if add_name:
                        add_fq = add_name if "." in add_name else ".".join([self._additive(x) for x in ns] + [add_name]) if ns else add_name
                    else:
                        add_fq = self._additive(fq)
                    if add_fq != fq:
                        self._add(add_fq, mod, m.group("kind"), f"(to_additive of {fq}) " + self._additive(sigtext))
            elif s and not s.startswith(("--", "/-", "@[")) and not s.endswith("-/"):
                pending_attr = ""   # ordinary code line: any dangling attribute no longer applies
            i += 1

    def lookup(self, name: str) -> tuple[str, str] | None:
        hit = self.by_name.get(name)
        if hit:
            return (hit[0], hit[2])
        return None

    def suggest(self, name: str, limit: int = 4) -> list[str]:
        last = name.split(".")[-1]
        cands = list(self.by_last.get(last, []))
        if len(cands) < limit:  # same namespace, similar last component
            prefix = ".".join(name.split(".")[:-1])
            import difflib
            pool = [n for n in self.by_name if n.startswith(prefix + ".")] if prefix else []
            cands += difflib.get_close_matches(name, pool, n=limit, cutoff=0.8)
        return list(dict.fromkeys(cands))[:limit]


DECL_RE_ANY = re.compile(rf"\b{DECL_KINDS}\b")
_INDEX = DeclIndex()


def decl_index() -> DeclIndex:
    if not _INDEX.ready:
        _INDEX.build()
    return _INDEX


def find_decl(name: str) -> tuple[str, str] | None:
    """Locate a declaration by fully qualified name → (module, signature) or None.
    Core (`Init.*`) modules are always available; Mathlib/Batteries modules may need an import."""
    name = name.strip().strip("`")
    if not name:
        return None
    if name in _decl_cache:
        return _decl_cache[name]
    hit = decl_index().lookup(name)
    _decl_cache[name] = hit
    return hit


def verify_names(names: list[str]) -> str:
    """Human-readable verification block for a list of candidate declaration names."""
    lines = ["DECLARATION CHECK (approximate local source index; confirm signatures with Lean):"]
    for n in dict.fromkeys(names):
        hit = find_decl(n)
        if hit:
            where = "core, always available" if hit[0].startswith("Init") else hit[0]
            lines.append(f"  ✓ {n}  [{where}]\n      {hit[1]}")
        else:
            sug = decl_index().suggest(n)
            lines.append(f"  ✗ {n}  — NOT FOUND (may be generated or absent; check with Lean)" + (f"; similar existing names: {', '.join(sug)}" if sug else ""))
    return "\n".join(lines)


NAME_RE = re.compile(r"\b((?:[A-Z][A-Za-z0-9_']*\.)+[a-zA-Z][A-Za-z0-9_'!?]*)\b")


def candidate_names(text: str, limit: int = 30) -> list[str]:
    """Namespaced identifiers that look like Mathlib declaration names (Nat.succ_le_iff, Finset.sum_range_succ)."""
    seen = []
    for m in NAME_RE.finditer(text):
        n = m.group(1)
        if n.startswith(("Mathlib.", "Lean.", "Std.", "IO.")) or n.count(".") > 3:
            continue
        if n not in seen:
            seen.append(n)
        if len(seen) >= limit:
            break
    return seen


# Lean has used several phrasings: "unknown identifier 'X'", "unknown constant 'X'", and (4.2x+) "The identifier `X` is unknown".
UNKNOWN_RE = re.compile(r"unknown (?:identifier|constant|namespace) [`']([^`']+)[`']|[Tt]he identifier `([^`]+)` is unknown|Unknown (?:identifier|constant) `([^`]+)`")


def unknown_names_from_errors(errors: list[str]) -> list[str]:
    out = []
    for e in errors:
        for groups in UNKNOWN_RE.findall(e):
            n = next((g for g in groups if g), None)
            if n and n not in out:
                out.append(n)
    return out


def module_exists(mod: str) -> bool:
    if mod.startswith("Init."):
        return True   # Lean core: always loaded, never needs an import line
    if mod.startswith("Batteries."):
        return (FORMAL / ".lake" / "packages" / "batteries" / (mod.replace(".", os.sep) + ".lean")).exists()
    return (MATHLIB_SRC.parent / (mod.replace(".", os.sep) + ".lean")).exists()


def needs_import(mod: str) -> bool:
    return module_exists(mod) and not mod.startswith("Init.")


def suggest_module(mod: str, limit: int = 3) -> list[str]:
    """Fuzzy help for a mis-remembered module name: modules sharing the last component."""
    last = mod.split(".")[-1]
    hits = []
    try:
        for p in MATHLIB_SRC.rglob(f"{last}.lean"):
            hits.append(module_of_path(str(p)))
            if len(hits) >= limit:
                break
    except Exception:
        pass
    return hits


# --------------------------------------------------------------------------- knowledge (self-improvement)

def playbook_entries() -> list[dict]:
    """knowledge/playbook.md holds one lesson per bullet: `- [tags: a, b] lesson text` (tags optional).
    Entries are appended by the `retrospect` stage after runs and hand-curated; `harness.py regress`
    guards against regressions when they change prompts' behavior."""
    path = KNOWLEDGE / "playbook.md"
    if not path.exists():
        return []
    entries = []
    for chunk in re.split(r"\n(?=- )", path.read_text()):
        chunk = chunk.strip()
        if not chunk.startswith("- "):
            continue
        m = re.match(r"- \[tags:\s*([^\]]*)\]\s*(.*)", chunk, re.S)
        tags = [t.strip().lower() for t in m.group(1).split(",")] if m else []
        text = (m.group(2) if m else chunk[2:]).strip()
        entries.append({"tags": tags, "text": " ".join(text.split())})
    return entries


def playbook_for(query: str, cap_chars: int = 3000, max_entries: int = 12) -> str:
    entries = playbook_entries()
    if not entries:
        return ""
    words = {w.lower() for w in re.findall(r"[A-Za-z][A-Za-z_']{2,}", query)}
    def score(e):
        if "always" in e["tags"]:
            return 10**6
        hits = sum(1 for t in e["tags"] if t in words or any(t in w for w in words))
        hits += sum(1 for w in set(re.findall(r"[A-Za-z][A-Za-z_']{3,}", e["text"].lower())) if w in words) * 0.2
        return hits
    ranked = sorted(entries, key=score, reverse=True)
    out, total = [], 0
    for e in ranked[:max_entries]:
        if score(e) <= 0 and total > 0:
            break
        line = "- " + e["text"]
        if total + len(line) > cap_chars:
            break
        out.append(line); total += len(line)
    if not out:
        return ""
    return "PLAYBOOK (lessons the harness learned from earlier runs; apply when relevant):\n" + "\n".join(out)


def harvest_lemmas(proof: str, pid: str, run_id: str):
    """Store every helper lemma of a verified proof in knowledge/lemmas.jsonl for retrieval by later runs."""
    KNOWLEDGE.mkdir(exist_ok=True)
    out = KNOWLEDGE / "lemmas.jsonl"
    seen = set()
    if out.exists():
        for l in out.read_text().splitlines():
            try:
                seen.add(json.loads(l)["statement"])
            except Exception:
                pass
    blocks = re.split(r"\n(?=(?:private\s+|protected\s+)?(?:lemma|theorem)\s)", proof)
    n = 0
    with open(out, "a") as f:
        for b in blocks:
            m = re.match(r"(?:private\s+|protected\s+)?(?:lemma|theorem)\s+(\S+)(.*?):=", b, re.S)
            # skip only the main theorem itself (erdos_NNN); helpers are often named erdos_NNN_key etc.
            if not m or re.fullmatch(r"erdos_\d+", m.group(1)):
                continue
            stmt = " ".join((m.group(1) + m.group(2)).split())
            if stmt in seen:
                continue
            f.write(json.dumps({"name": m.group(1), "statement": stmt, "code": b.strip(), "problem": pid,
                                "run": run_id, "imports": explicit_imports(proof)}) + "\n")
            n += 1
    return n


def lemmas_for(query: str, limit: int = 6) -> str:
    path = KNOWLEDGE / "lemmas.jsonl"
    if not path.exists():
        return ""
    words = {w.lower() for w in re.findall(r"[A-Za-z][A-Za-z_']{2,}", query)}
    scored = []
    for l in path.read_text().splitlines():
        try:
            e = json.loads(l)
        except Exception:
            continue
        s = sum(1 for w in set(re.findall(r"[A-Za-z][A-Za-z_']{3,}", e["statement"].lower())) if w in words)
        if s > 0:
            scored.append((s, e))
    scored.sort(key=lambda t: -t[0])
    if not scored:
        return ""
    lines = ["HELPER FRAGMENTS FROM CHECKED PROOFS (not independently checked; may require earlier definitions, helpers, and imports):"]
    for _, e in scored[:limit]:
        needs = [m for m in e.get("imports", []) if m not in DEFAULT_IMPORTS]
        note = f"-- needs: -- IMPORTS: {' '.join(needs)}\n" if needs else ""
        lines.append(f"```lean\n{note}{e['code']}\n```")
    return "\n".join(lines)


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
    -- READ: Mathlib.Combinatorics.Hindman        (read a source module, including definitions and theorem arguments)
    -- CHECK: Nat.some_lemma Finset.other_lemma     (verifies that these names exist and shows their signatures)
  The harness executes them and returns results next round.
- If you use a name the harness cannot find, it tells you so (with similar real names); if a name exists in a
  Mathlib module that is not imported, the harness adds the import automatically — so never guess module
  names, and prefer well-known Mathlib lemma names.
- Large numerals: never let `decide` evaluate huge terms (n! for n ≥ 10, x^x, ...). Use `norm_num [Nat.factorial]`
  or `decide +kernel` for exhaustive finite checks, and give witnesses in factored form when exponent
  arithmetic is involved."""


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


PROVE_STRATEGIES = [
    "Look hard for an existing Mathlib lemma that is (or nearly is) this statement; the retrieval hits below are a starting point. Glue with simp/norm_num/omega.",
    "Elementary direct argument: unfold definitions, then induction or strong induction with omega/norm_num closing the goals.",
    "Case analysis: split on small cases (interval_cases / decide for finite checks) plus a general argument for the tail.",
    "Contradiction or extremal argument: assume the negation, extract a witness, derive a contradiction with nlinarith/omega and monotonicity lemmas.",
]


def prove_prompt(problem: dict, statement: str, literature: str, retrieval: list[str],
                 history: str, round_i: int, m: int, imports: list[str], repair: str = "",
                 verified: str = "", playbook: str = "") -> str:
    strat = PROVE_STRATEGIES[(round_i - 1) % len(PROVE_STRATEGIES)]
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

{verified}

Retrieval results:
{ret}

{playbook}

{history}

{repair}

Primary strategy for this round: {strat}
Produce {m} attempts. Each attempt = one complete file body in its own ```lean block (helpers + the
frozen theorem with a real proof replacing `sorry`). Before each block, write a line `ATTEMPT k: <one-line plan>`.
Make the attempts genuinely different, not cosmetic variations. If a REPAIR CONTEXT is given, at least one
attempt must be a minimal, targeted repair of the most promising failed attempt (fix exactly what the
compiler complained about; keep what worked). A partial proof that compiles with `sorry` in a clearly
isolated helper lemma is worth more than a from-scratch attempt that does not compile.

{HOUSE_RULES}"""


def agentic_prompt(problem: dict, statement: str, literature: str, repair: str, verified: str,
                   imports: list[str], max_turns: int, playbook: str = "", tool_backend: str = "claude-cli",
                   previous: str = "", critic: str = "", search: str = "") -> str:
    previous_block = ("PREVIOUS SESSION — this sandbox CONTINUES from the best earlier session (its Attempt.lean and scratch "
                      "files are here); its final summary:\n" + previous.strip()) if previous.strip() else ""
    if tool_backend == "codex-cli":
        access = ("You may use read-only shell commands such as rg, sed, cat, and ls to inspect this "
                  "sandbox and the Mathlib source directory below. Edit only Attempt.lean or scratch "
                  ".lean files in this sandbox, using the available file-editing tools. "
                  "Compile only through ./check.sh. Do not read other harness runs, knowledge/solved, "
                  "reference proofs, credentials, or unrelated files; do not access the network.")
        budget_note = f"The session timeout is the enforced budget; aim for at most {max_turns} tool calls."
    else:
        access = ("Use Read/Grep/Glob tools for source inspection. ./check.sh is the only allowed "
                  "shell command; use Edit/Write for sandbox proof files.")
        budget_note = f"You have at most {max_turns} tool calls."
    return f"""You are proving a theorem in Lean 4 + Mathlib inside a sandbox directory (your cwd).

FILES HERE:
  Attempt.lean  — the file to complete. It already has the import header and the FROZEN theorem statement
                  (with `sorry`). Edit it in place.
  check.sh      — `./check.sh Attempt.lean` compiles the file against Mathlib (takes ~30-60 s; prints errors,
                  warnings, and `exit=<code>`).
  TASK.md       — this brief.
{access}
Mathlib sources for reading/grepping:
  {MATHLIB_SRC}
  e.g. Grep for `theorem prod_range_succ` under Mathlib/Algebra/BigOperators to confirm names and signatures.

ENGLISH PROBLEM (erdosproblems.com #{problem['id']}):
{problem['statement']}

KNOWN-RESOLUTION CONTEXT:
{literature or '(none)'}

FROZEN THEOREM (do not change its name, binders, or goal; helpers go ABOVE it):
```lean
{statement}
```

{verified}

{playbook}

{repair}

{search}

{previous_block}

{critic}

WORKFLOW ({budget_note}):
1. Plan the mathematical argument first; decide helper lemmas.
2. Edit Attempt.lean, run ./check.sh Attempt.lean, read the errors, fix, repeat. Compile often; small steps.
3. You may add `import Mathlib.Some.Module` lines at the top if a lemma needs one (the header already
   imports {', '.join(imports)}). Do not remove `set_option maxHeartbeats`.
4. Success requires exit=0, no compiler errors (including error(...) diagnostics), and no sorry warnings.
5. When done (or when you are about to run out of budget), reply with the COMPLETE final contents of
   Attempt.lean in one ```lean block, followed by a line `RESULT: compiled` or `RESULT: not-compiled` and
   1-3 lines on what remains if anything.

RULES: never use `axiom`, `native_decide`, `unsafe`, `admit`; `sorry` only in intermediate states; do not
touch any file other than Attempt.lean (you may create scratch .lean files here to test lemmas separately,
checking them with ./check.sh). Never let `decide` evaluate huge terms; prefer `norm_num`, `omega`, `simp`,
`ring`, `nlinarith`, `positivity`, `interval_cases`, `decide +kernel` for exhaustive finite checks."""


CRITIC_PROMPT = """You are a critical reviewer inside a Lean 4 proof harness. Below are the frozen theorem and a digest of the
attempts that failed so far (plans, code, compiler errors). In at most 8 bullets, say: (1) which plan was closest
and exactly what broke it, (2) which lemma names / encodings were wrong and what to use instead, (3) one concrete
alternative route if the current one looks doomed, (4) a checklist of things the next session must verify with
the compiler EARLY (small lemmas first). Be specific and terse; no restatement of the problem.

FROZEN THEOREM:
```lean
{statement}
```

FAILED ATTEMPTS DIGEST:
{digest}"""


ASSESS_PROMPT = """You are the triage stage of a Lean 4 harness for Erdős problems. Classify the task so the harness can route it.
Answer from the statement, the literature notes and your knowledge; do not attempt the proof.

ENGLISH PROBLEM (erdosproblems.com #{pid}, status per site: {status}):
{statement_en}

Site notes: {notes}

LITERATURE STAGE OUTPUT:
{literature}

FROZEN FORMAL STATEMENT (the exact target):
```lean
{statement}
```

Respond with EXACTLY one ```json block with these keys:
{{
  "shape": "witness | finite-check | infinitude | universal | density-asymptotic | extremal-bound | structural",
  "status": "resolved | open | ambiguous",
  "depth": "trivial | elementary | medium | research",
  "computable": true or false   (a BOUNDED computation could decide the target or exhibit a witness/counterexample),
  "known_bound": "best known bound/partial result as a short string, or null",
  "routes": ["2-4 short proof-route ideas"],
  "recommended_mode": "fast | search-first | construct | research",
  "budget_tier": "S | M | L",
  "rationale": "one sentence"
}}
Definitions: shape=witness means the target is (or reduces to) exhibiting explicit objects; finite-check means a
finite exhaustive verification; infinitude means an infinite family must be produced; universal means a
for-all statement to prove; extremal-bound means improving/attaining a numerical bound; depth=trivial means a
one-liner once the witness is known, elementary means a page of undergraduate mathematics, research means it
needs ideas beyond textbook methods."""


SEARCH_PROMPT = """You are the computational-search stage of a Lean 4 harness. Write ONE self-contained Python 3 script that
searches for a {kind} of the FROZEN statement below by bounded brute force / structured enumeration.

ENGLISH PROBLEM (erdosproblems.com #{pid}):
{statement_en}

Notes: {notes}

FROZEN FORMAL STATEMENT:
```lean
{statement}
```

Requirements:
- Pure standard library only: math, itertools, functools, collections, fractions, random, time, heapq, bisect, json, re.
  NO file, network, os, sys (not even for the recursion limit), subprocess or other imports; no input(); nothing interactive.
- Hard limits: stop after {cap_seconds} seconds of wall-clock or ~{cap_candidates} candidates, whichever first.
- Search the SMALLEST candidates first (a Lean certificate by `decide +kernel` / `norm_num` must stay cheap):
  prefer witnesses below 10^6 and avoid enormous exponents; if the statement involves n!, powers or products,
  compute exactly with Python integers.
- On success print exactly one line `WITNESS: <json object>` mapping each bound variable of the statement to its
  value (integers, lists of integers, or strings for expressions); then exit. If nothing is found print `NONE`.
- Print at most 20 progress lines. The script must be a ```python fenced block and nothing else needs explaining.
Read the quantifiers carefully: a {kind} means {kind_expl}."""


WEB_LITERATURE_ADDENDUM = """

WEB SOURCES (use WebFetch/WebSearch; at most 6 fetches): https://www.erdosproblems.com/{pid} ,
https://www.erdosproblems.com/forum/thread/{pid} , and arXiv/MathOverflow for partial results. Extract the best
known partial results and bounds. Do NOT open Lean proof repositories (plby/lean-proofs, formal-conjectures) and do
not quote Lean code. End your report with one line `KNOWN_BOUND: <best known bound / partial result, or none>`."""


CONSTRUCT_PROMPT = """You are the construction-search stage of a Lean 4 harness (iteration {iteration}). The target is an
extremal / bound-type statement; we search numerically for good finite objects and certify the best one in Lean.

ENGLISH PROBLEM (erdosproblems.com #{pid}):
{statement_en}

Notes: {notes}

FROZEN FORMAL TARGET (context only; the certificate below is about a concrete finite object, not this theorem):
```lean
{statement}
```

Best known bound / partial result: {known}
Archive of the best objects so far (score, description): {archive}
Current program (improve it; keep the interface):
```python
{program}
```

Write ONE ```python module (standard library only: math, itertools, functools, collections, fractions, random, heapq,
bisect) defining:
  PARAM_SPACE: dict[str, list]              # discrete choices the driver samples from
  def generate(params: dict, rng) -> object # a concrete finite object (JSON-serializable: ints / lists / dicts)
  def valid(obj) -> bool                    # the defining property holds (checked exactly, in Python)
  def score(obj) -> float                   # higher is better; comparable with the known bound (state the unit in describe)
  def mutate(obj, rng) -> object            # small random modification (local search)
  def describe(obj) -> str                  # one line: size / bound achieved / parameters
  def lean_certificate(obj) -> str          # Lean 4 + Mathlib snippet certifying the finite property of THIS obj, NO `sorry`,
                                            # `-- IMPORTS: Mathlib.X` lines allowed at the top. It must compile within ~10 minutes:
                                            # write the check as a `def construct_check : Bool := ...` over explicit `List ℕ` data
                                            # (loops via List.all / List.any / decide on small ℕ comparisons) and prove
                                            # `theorem construct_cert : construct_check = true := by decide +kernel` (kernel
                                            # reduction of Bool programs is fast; `decide` on Prop over `Finset.powersetCard` is
                                            # NOT — a 3000-subset check timed out). `native_decide` is banned. Keep the total
                                            # work under ~10^6 basic steps; if the object is too big to certify, shrink it.
Constraints: every function must be fast (the driver evaluates thousands of candidates within {iteration}·seconds);
objects should stay small enough for a Lean `decide` certificate. Prefer structured constructions (modular, greedy,
algebraic) over blind randomness, and explain the idea in a short comment at the top."""


CONSTRUCT_DRIVER = r'''
import json, random, time, math, itertools, functools, collections, fractions, heapq, bisect
cfg = json.load(open("config.json"))
ns = {}
exec(open("program.py").read(), ns)
rng = random.Random(cfg.get("seed", 0))
t_end = time.time() + cfg.get("seconds", 120)
PARAM_SPACE = ns.get("PARAM_SPACE", {})
gen, valid, score, mutate, describe, cert = (ns.get(k) for k in ("generate", "valid", "score", "mutate", "describe", "lean_certificate"))
archive = []
def consider(obj, how):
    try:
        if not valid(obj):
            return
        s = float(score(obj))
    except Exception:
        return
    archive.append({"score": s, "object": obj, "describe": (describe(obj) if describe else "")[:300], "how": how})
    archive.sort(key=lambda a: -a["score"])
    del archive[12:]
# seed from previous archive objects (if the program still accepts them)
for a in cfg.get("archive_in", []):
    consider(a.get("object"), "carried")
n = 0
keys = list(PARAM_SPACE)
while time.time() < t_end:
    params = {k: rng.choice(PARAM_SPACE[k]) for k in keys}
    try:
        obj = gen(params, rng)
    except Exception:
        n += 1
        continue
    consider(obj, f"generate {params}")
    if mutate and archive and rng.random() < 0.5:
        base = rng.choice(archive[:5])["object"]
        for _ in range(20):
            if time.time() >= t_end:
                break
            try:
                m = mutate(base, rng)
            except Exception:
                break
            consider(m, "mutate")
            if archive and archive[0]["object"] == m:
                base = m
    n += 1
    if n > 2_000_000:
        break
for a in archive[:5]:
    try:
        a["certificate"] = cert(a["object"]) if cert else ""
    except Exception as e:
        a["certificate"] = ""
print("EVALUATED:", n)
print("ARCHIVE:" + json.dumps(archive[:5]))
'''


EXPERIMENTS_PROMPT = """You are the numerical-experiments stage of a research program on an OPEN Erdős problem (#{pid}).

ENGLISH PROBLEM:
{statement_en}

FROZEN FORMAL TARGET:
```lean
{statement}
```

LITERATURE:
{literature}

CURRENT PLAN:
{plan}

Write ONE ```python script (standard library only: math, itertools, functools, collections, fractions, random, heapq,
bisect, json, re; NO sys/os/files/network — do not import `sys` even for the recursion limit; use iteration instead)
that tests 2-3 concrete conjectures or special cases relevant to the plan numerically (small parameters first, ≤ 60 s
total; print ≤ 20 informative lines, each starting with `EXP:`). State each tested conjecture in a comment above its code."""


PLAN_PROMPT = """You are the planning stage of a research program on an OPEN Erdős problem (#{pid}), cycle {cycle}.

ENGLISH PROBLEM:
{statement_en}

FROZEN FORMAL TARGET (the ultimate goal; nobody expects it this cycle):
```lean
{statement}
```

LITERATURE: {literature}

PREVIOUS PLAN: {plan}

EXPERIMENT OUTPUT (this cycle): {experiments}

CERTIFIED LEMMAS SO FAR (Lemmas.lean, importable as a module by every attempt):
```lean
{lemmas}
```

LEDGER (what was attempted): {ledger}

Produce (1) an updated plan in ONE ```markdown block: conjectures with status (supported / refuted / open), special
cases done, sub-goals with priorities and why each moves toward the target; (2) 3-5 concrete Lean 4 sub-statements
as separate ```lean blocks, each `theorem erdos_{pid}_sub<k>_<i> ... := by\n  sorry`, self-contained (own `def`s if
needed, no `import` lines; `-- IMPORTS:` directives allowed), individually provable by elementary means or from the
certified lemmas — small special cases (n ≤ k), weaker bounds, structural lemmas. Do not restate proved lemmas.

""" + HOUSE_RULES


NEGATION_PROMPT = """The Lean 4 theorem below is a frozen formalization of an OPEN conjecture (Erdős #{pid}). Write its exact logical
NEGATION as a theorem named `erdos_{pid}_neg` with the SAME `def`s (copy them verbatim above it) and the goal
`¬ (<the full proposition of erdos_{pid}, with all binders turned into ∀>)`. Do not simplify or push the negation
inward; do not change any definition. Output exactly one ```lean block ending in `:= by\n  sorry`.

```lean
{statement}
```"""


def decide_mode(a: dict, args, problem: dict | None = None) -> tuple[str, str]:
    """Routing rules for the triage stage (flags override). Returns (mode, reason)."""
    forced = getattr(args, "mode", None)
    if forced:
        return forced, "forced by --mode"
    shape = str(a.get("shape") or "").lower().strip()
    status = str(a.get("status") or "").lower().strip()
    depth = str(a.get("depth") or "").lower().strip()
    computable = a.get("computable") is True
    routes = " ".join(str(r) for r in (a.get("routes") or [])).lower()
    improve_bound = ("bound" in routes and "improv" in routes) or (shape == "extremal-bound")
    site_class = str((problem or {}).get("class") or "").lower()
    if status == "resolved" and depth in ("trivial", "elementary"):
        return "fast", "resolved + trivial/elementary"
    if site_class in ("falsifiable", "verifiable", "decidable") and status != "resolved":
        # erdosproblems.com itself says a finite computation could settle or exhibit it — stronger than the model's guess
        return "search-first", f"site class {site_class} (a bounded computation could decide/exhibit it)"
    if shape in ("witness", "finite-check") or computable:
        return "search-first", f"shape={shape or '?'}, computable={computable}"
    if shape == "extremal-bound" or (status == "open" and improve_bound):
        if getattr(args, "allow_construct", False):
            return "construct", "extremal/bound target and --allow-construct"
        return "fast", "extremal/bound target but --allow-construct not set: fast path, then partial results"
    if status == "open" and depth == "research":
        if getattr(args, "allow_research", False):
            return "research", "open + research depth and --allow-research"
        return "fast", "open + research depth without --allow-research: fast+agentic+decompose, then partial results"
    return "fast", f"default (status={status or '?'}, depth={depth or '?'}, shape={shape or '?'})"


def statement_shape(statement: str) -> str | None:
    """'witness' if the frozen goal is existential (∃ … / ¬ ∀ …), 'counterexample' if universal (∀ … / binders), else None."""
    body = strip_comment_lines(statement)
    m = re.search(r"theorem\s+\S+(.*?):=\s*by", body, re.S)
    if not m:
        return None
    header = m.group(1)
    # theorem headers are `name <bracketed binders> : goal`; the goal starts at the FIRST depth-0 colon
    depth, cut = 0, None
    for i, ch in enumerate(header):
        if ch in "([{⦃": depth += 1
        elif ch in ")]}⦄": depth -= 1
        elif ch == ":" and depth == 0 and header[i:i + 2] != ":=":
            cut = i
            break
    goal = header[cut + 1:].strip() if cut is not None else header.strip()
    binders = header[:cut].strip() if cut is not None else ""
    if re.match(r"^(∃|¬\s*∀|Set\.Nonempty|.*\.Nonempty\b)", goal):
        return "witness"
    if re.match(r"^(∀|¬\s*∃)", goal) or binders:
        return "counterexample"
    if re.match(r"^Set\.Infinite|^.*\.Infinite\b", goal):
        return "witness"   # an infinite family: a witness for a large parameter is still informative
    return None


ALLOWED_PY_MODULES = {"math", "itertools", "functools", "collections", "fractions", "random", "time", "heapq",
                      "bisect", "operator", "string", "typing", "dataclasses", "decimal", "statistics", "array",
                      "json", "re"}
FORBIDDEN_PY_TOKENS = re.compile(r"__import__|\bopen\s*\(|\bexec\s*\(|\beval\s*\(|\bcompile\s*\(|\binput\s*\(|\bos\.|\bsys\.|"
                                 r"subprocess|socket|shutil|pathlib|urllib|requests|ctypes|signal\.|threading|multiprocessing|"
                                 r"importlib|builtins|globals\s*\(|getattr\s*\(")


def unsafe_python(code: str) -> str | None:
    """Static screen for the model-written search script: stdlib math/itertools-style modules only, no I/O, no OS."""
    for line in code.splitlines():
        s = line.strip()
        m = re.match(r"^import\s+(.+)$", s)
        if m:
            for mod in m.group(1).split(","):
                base = mod.strip().split(" as ")[0].split(".")[0].strip()
                if base and base not in ALLOWED_PY_MODULES:
                    return f"import {base}"
            continue
        m = re.match(r"^from\s+([A-Za-z_][\w.]*)\s+import\b", s)
        if m:
            base = m.group(1).split(".")[0]
            if base not in ALLOWED_PY_MODULES:
                return f"from {base} import"
            continue
        t = FORBIDDEN_PY_TOKENS.search(s)
        if t:
            return t.group(0)
    return None


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

If compiler errors are present, repair those errors in the CURRENT FILE first, preserving completed
proofs and the construction. This includes files with no `sorry`: they are not finished until they
compile. Prefer small local corrections over replacing the proof strategy. If the file compiles,
replace at least the first remaining `sorry` with a real proof (more if confident).
Keep the final theorem's statement identical. Output EXACTLY
one ```lean block with the full updated file body.

{HOUSE_RULES}"""


def backtranslate_prompt(statement: str) -> str:
    return f"""Translate this Lean 4 theorem statement into precise plain-English mathematics.
State exactly what is being claimed — quantifiers, domains, bounds. Do not mention Lean or code.
Do not editorialize. 2-5 sentences.

```lean
{statement}
```"""


def compare_prompt(problem: dict, backtranslation: str, direction: str | None = None) -> str:
    if direction in ("pos", "neg"):
        want = ("exactly the conjecture/question of A answered YES (the assertion as stated)" if direction == "pos"
                else "exactly the NEGATION of the conjecture/question of A (the assertion as stated is false)")
        return f"""Two mathematical statements follow. Problem A is OPEN; the harness attacks both directions separately.
Decide whether statement B is {want}. Be adversarial about quantifier order, domains, edge cases (n=0/1),
strict vs non-strict bounds, and hidden strengthening/weakening.

STATEMENT A (open Erdős problem #{problem['id']}):
{problem['statement']}

Site notes: {problem.get('notes', '(none)')}

STATEMENT B (independent back-translation of the frozen formalization for direction `{direction}`):
{backtranslation}

Respond with EXACTLY one ```json block: {{"faithful": true|false, "issues": ["..."], "verdict": "<one sentence>"}}
"faithful" means: a proof of B would legitimately settle A in the `{direction}` direction."""
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
    return "\n".join(l for l in src.splitlines()
                     if not (l.strip().startswith("import ") or l.strip().startswith("set_option maxHeartbeats")
                             or l.strip().startswith("set_option autoImplicit"))).strip()


def import_lines(src: str) -> list[str]:
    """Real `import X` lines (the agentic sandbox lets the model write them); treated like `-- IMPORTS:`."""
    return [tok for l in src.splitlines() if l.strip().startswith("import ")
            for tok in l.strip()[len("import "):].split() if IMPORT_RE.match(tok) or tok.startswith("Batteries.")]


def explicit_imports(body: str) -> list[str]:
    return list(dict.fromkeys(extract_directive_imports(body) + import_lines(body)))


def norm_ws(s: str) -> str:
    return " ".join(s.split())


def strip_comment_lines(s: str) -> str:
    """Mask nested Lean comments and strings, preserving token boundaries and newlines.

    This is lexical screening, not a substitute for checking the elaborated theorem type.
    """
    out = []
    i, depth, string = 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith("/-", i):
                depth += 1
                out.append("  "); i += 2
            elif s.startswith("-/", i):
                depth -= 1
                out.append("  "); i += 2
            else:
                out.append("\n" if s[i] == "\n" else " "); i += 1
        elif string:
            if s[i] == "\\" and i + 1 < len(s):
                out.append("  "); i += 2
            elif s[i] == '"':
                string = False
                out.append(" "); i += 1
            else:
                out.append("\n" if s[i] == "\n" else " "); i += 1
        elif s.startswith("/-", i):
            depth = 1
            out.append("  "); i += 2
        elif s.startswith("--", i):
            end = s.find("\n", i)
            end = len(s) if end == -1 else end
            out.append(" " * (end - i)); i = end
        elif s[i] == '"':
            start = i
            i += 1
            while i < len(s):
                if s[i] == "\\":
                    i += 2
                elif s[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            # Preserve literal identity without letting quoted code satisfy a guard.
            out.append(" __LEAN_STRING_" + hashlib.sha256(s[start:i].encode()).hexdigest() + " ")
        else:
            out.append(s[i]); i += 1
    return "".join(out)


def hole_count(source: str) -> int:
    return len(re.findall(r"\bsorry\b", strip_comment_lines(source)))


def extract_directive_imports(body: str) -> list[str]:
    out = []
    for line in re.findall(r"^--\s*IMPORTS?:\s*(.+)$", body, re.M):
        for tok in line.replace(",", " ").split():
            if IMPORT_RE.match(tok):
                out.append(tok)
    return out


def compose(body: str, imports: list[str]) -> str:
    extra = explicit_imports(body)
    body = strip_imports(body)
    imps = list(dict.fromkeys(imports + extra))
    header = "\n".join(f"import {m}" for m in imps)
    # autoImplicit MUST be off: `lake env lean` on a standalone file ignores the project's lakefile options,
    # and with Lean's default an unknown identifier inside a theorem STATEMENT is silently auto-bound as an
    # implicit variable — a misspelled `Nat.Prime` would compile as a vacuous/different theorem instead of
    # failing with `unknown identifier`. (Found by the mock pipeline test.)
    return f"{header}\n\nset_option maxHeartbeats 1000000\nset_option autoImplicit false\n\n{body}\n"


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
        if allow_sorry and name == "sorry":
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
            self.run_dir = RUNS / f"{datetime.now().strftime('%Y%m%d-%H%M%S-%f')}-erdos{pid}"
        self.run_dir.mkdir(parents=True, exist_ok=True)
        cur = RUNS / "current"
        link = RUNS / f".current-{uuid.uuid4().hex}"
        link.symlink_to(self.run_dir)
        link.replace(cur)
        self.log = RunLog(self.run_dir)
        self.state_path = self.run_dir / "state.json"
        self.state = json.loads(self.state_path.read_text()) if self.state_path.exists() else {}
        previous_problem = self.state.get("problem_input")
        if previous_problem is not None and previous_problem != self.problem:
            raise ValueError("resume problem differs from the checkpoint; start a new run")
        self.state["problem_input"] = self.problem
        self.state.setdefault("invocations", []).append({
            "at": now(), "backend": args.backend, "model": args.model,
            "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rounds": args.rounds, "samples": args.samples,
            "decompose_rounds": args.decompose_rounds,
        })
        self.lean = LeanChecker(FORMAL, args.lean_timeout)
        if args.backend == "claude-cli":
            self.llm = ClaudeCliBackend(args.model, args.llm_timeout, args.call_budget,
                                        aux_effort=getattr(args, "effort_aux", "medium"),
                                        formal_effort=getattr(args, "effort_formal", "high"),
                                        prove_effort=getattr(args, "effort_prove", None),
                                        aux_budget_usd=getattr(args, "aux_budget", 2.5),
                                        formal_budget_usd=getattr(args, "formal_budget", 4.0))
        elif args.backend == "codex-cli":
            self.llm = CodexCliBackend(args.model, args.llm_timeout)
        else:
            self.llm = FileBackend(self.run_dir, args.llm_timeout)
        self.args = args
        self.checks = 0
        self.imports = list(self.problem.get("imports", DEFAULT_IMPORTS))
        # imports auto-added in an earlier (resumed) invocation stay in force
        self.imports = list(dict.fromkeys(self.imports + self.state.get("auto_imports", [])))
        self._lock = threading.Lock()
        self.t0 = time.time()
        self.thm_name = f"erdos_{pid}"      # `erdos_N_neg` for the negation child in --open mode
        self.direction = None               # "pos" / "neg" for --open children (their proofs never enter knowledge/solved)
        if not _INDEX.ready:
            _INDEX.build(self.log)

    class BudgetExhausted(Exception):
        """Raised when the run's total spend crosses --run-budget; callers finish cleanly with exit 2."""

    def spent_usd(self) -> float:
        """Total logged spend of this run (all invocations, survives --resume)."""
        try:
            return sum(float(json.loads(l).get("cost_usd") or 0) for l in open(self.log.path) if '"response"' in l)
        except Exception:
            return getattr(self.llm, "total_cost_usd", 0.0)

    def _check_run_budget(self, purpose: str):
        budget = getattr(self.args, "run_budget", None)
        if budget and self.spent_usd() >= budget:
            self.log.event("run", "budget_exhausted", after=purpose, spent_usd=round(self.spent_usd(), 2), budget=budget)
            raise Harness.BudgetExhausted(f"run budget ${budget} exhausted (spent ${self.spent_usd():.2f})")

    def playbook_block(self, extra_text: str = "") -> str:
        """Relevant entries from knowledge/playbook.md and knowledge/lemmas.jsonl (accumulated lessons)."""
        q = self.problem["statement"] + "\n" + self.state.get("statement", "") + "\n" + extra_text
        parts = [p for p in (playbook_for(q), lemmas_for(q)) if p]
        return "\n\n".join(parts)

    # -- infrastructure

    def save(self):
        if getattr(self, "state_path", None) is None:
            return   # partially constructed object (tests stub stages); nothing to persist
        review_dir = self.state_path.parent
        self.state['direction'] = getattr(self, 'direction', self.state.get('direction'))
        self.state['review_context'] = {'imports': getattr(self, 'imports', [])}
        self.state['solution_review'] = milestones(
            self.problem, self.state, getattr(self, 'imports', []), environment_snapshot(FORMAL),
            load_attestations(review_dir))
        pending = self.state_path.with_suffix(".tmp")
        pending.write_text(json.dumps(self.state, indent=2))
        pending.replace(self.state_path)
        export_run(self.state_path.parent)

    def check(self, body: str, name: str) -> dict:
        """Compile `body` with the current import header. Two automatic repairs happen here so the LLM
        never has to spend a round on them:
          1. `-- IMPORTS:` directives naming non-existent modules are dropped (with a note in errors).
          2. `unknown identifier/constant 'X'` errors are resolved by grepping Mathlib for X; if X lives in
             a module we don't import yet, the module is added (for this run) and the file re-checked once.
        """
        with self._lock:
            self.checks += 1
        bad, notes = [], []
        for mod in explicit_imports(body):
            if not module_exists(mod):
                bad.append(mod)
                alt = suggest_module(mod)
                notes.append(f"import `{mod}` does not exist in this Mathlib"
                             + (f"; similar: {', '.join(alt)}" if alt else "") + " — dropped")
        if bad:
            body = "\n".join(l for l in body.splitlines()
                             if not ((re.match(r"^--\s*IMPORTS?:", l.strip()) or l.strip().startswith("import "))
                                     and any(b in l for b in bad)))
        src = compose(body, self.imports)
        res = self.lean.check(src, self.run_dir / "attempts" / f"{name}.lean")
        if not res["ok"] and not res.get("timeout"):
            unknown = unknown_names_from_errors(res["errors"])
            added = []
            for n in unknown[:6]:
                hit = find_decl(n)
                if hit and needs_import(hit[0]) and hit[0] not in self.imports \
                        and hit[0] not in explicit_imports(body):
                    if hit[0] not in added:
                        added.append(hit[0])
                    notes.append(f"auto-import: `{n}` lives in {hit[0]} — added to the header")
                elif not hit:
                    sug = decl_index().suggest(n)
                    notes.append(f"`{n}` is not a known declaration — do not use it"
                                 + (f"; similar existing names: {', '.join(sug)}" if sug else ""))
            if added:
                with self._lock:
                    self.imports = list(dict.fromkeys(self.imports + added))
                    self.state["auto_imports"] = sorted(set(self.state.get("auto_imports", []) + added))
                self.log.event("lean", "auto_import", name=name, modules=added)
                src = compose(body, self.imports)
                res = self.lean.check(src, self.run_dir / "attempts" / f"{name}.lean")
        # Notes are not compiler errors (they stay out of `errors`), but they are feedback the prover needs
        # ("`Foo` is not a known declaration; similar: ..."), so they travel with the attempt record too.
        res["notes"] = [f"harness note: {n}" for n in notes]
        if notes:
            res["infos"] = res["infos"] + res["notes"]
        res["body"] = body
        self.log.event("lean", "check", name=name, ok=res["ok"], sorries=res["sorries"],
                       n_errors=len(res["errors"]), first_error=(res["errors"][0] if res["errors"] else ""))
        return res

    PROOF_PURPOSES = {"prove", "refine", "decompose", "prove-agentic"}

    def ask(self, purpose: str, prompt: str) -> str:
        self.log.event("llm", "request", purpose=purpose, chars=len(prompt))
        t0 = time.time()
        try:
            text = self.llm.complete(purpose, prompt)
        except RuntimeError as e:
            # A per-call budget overrun on a NON-proof stage (formalize, judge, triage, …) is retried once at a
            # lower effort with a slightly larger cap; proof stages have their own escalation in stage_prove.
            if purpose in self.PROOF_PURPOSES or not re.search(r"budget", str(e), re.I) or not hasattr(self.llm, "_tuning"):
                raise
            effort, budget = self.llm._tuning(purpose)
            lower = "low" if effort in ("medium", "low") else "medium"
            self.log.event("llm", "budget_retry", purpose=purpose, effort=lower, budget=round(budget * 1.5, 2))
            text = self.llm.complete(purpose, prompt, effort_override=lower, budget_override=budget * 1.5)
        meta = getattr(self.llm, "last_meta", {}) or {}
        self.log.event("llm", "response", purpose=purpose, chars=len(text), secs=round(time.time() - t0, 1),
                       cost_usd=meta.get("cost_usd"), turns=meta.get("turns"), tokens=meta.get("tokens"))
        self._check_run_budget(purpose)
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
        if getattr(self.args, "literature_web", False) and hasattr(self.llm, "complete_web"):
            prompt = literature_prompt(self.problem) + WEB_LITERATURE_ADDENDUM.format(pid=self.problem["id"])
            self.log.event("llm", "request", purpose="literature-web", chars=len(prompt))
            t0 = time.time()
            text = self.llm.complete_web("literature", prompt, budget_usd=getattr(self.args, "web_budget", 3.0))
            meta = getattr(self.llm, "last_meta", {}) or {}
            self.log.event("llm", "response", purpose="literature-web", chars=len(text), secs=round(time.time() - t0, 1),
                           cost_usd=meta.get("cost_usd"), turns=meta.get("turns"), tokens=meta.get("tokens"))
            (self.run_dir / "transcripts").mkdir(exist_ok=True)
            n = len(list((self.run_dir / "transcripts").glob("*.md"))) + 1
            (self.run_dir / "transcripts" / f"{n:03d}-literature-web.md").write_text(f"# literature-web\n\n## prompt\n\n{prompt}\n\n## response\n\n{text}\n")
            if re.search(r"plby/lean-proofs|formal-conjectures|\.lean\b", text):
                # the model touched a Lean-proof source; drop the web result and fall back to knowledge-only
                self.log.event("literature", "forbidden_source_detected", detail="web literature discarded")
                text = ""
            m = re.search(r"KNOWN_BOUND:\s*(.+)", text)
            if m:
                self.state["known_bound"] = m.group(1).strip()[:300]
            if text.strip():
                self.state["literature"] = text.strip()
                self.save()
                self._check_run_budget("literature-web")
                return
        self.state["literature"] = self.ask("literature", literature_prompt(self.problem)).strip()
        self.save()

    def initial_retrieval(self) -> list[str]:
        """Seed retrieval: Mathlib's own Erdős-named theorems plus a verified-name check of every
        declaration the literature stage / problem notes mention. (The old version also ran loogle on the
        first 4 five-letter English words of the statement — 'there', 'exist', 'solutions' — pure noise
        that cost up to 80 s of web timeouts per stage.)"""
        hits = grep_mathlib(r"theorem .*[Ee]rdos", 10)
        names = candidate_names(self.state.get("literature", "") + "\n" + self.problem.get("notes", ""))
        if names:
            hits.append(verify_names(names[:20]))
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
            status = f"compiles with {a.get('n_sorries')} sorry" if a.get("compiled") else ""
            lines.append(f"- {a['name']} [{a['plan'][:100]}] {status}: {errs[:500]}")
        return "\n".join(lines)

    def _best_partials(self, attempts: list[dict], k: int = 2) -> list[dict]:
        """Rank complete candidates with a few errors ahead of compiling outlines; exclude
        timeouts and pre-compile rejections."""
        cands = [a for a in attempts if a.get("code") and not a.get("timeout") and not a.get("rejected")]
        def key(a):
            holes = hole_count(a["code"])
            errors = len(a.get("errors", []))
            # A complete construction with a few local errors deserves a repair
            # before an outline whose single hole may contain the whole theorem.
            near_complete = not a.get("compiled") and holes == 0 and 0 < errors <= 4
            return (0 if near_complete else 1 if a.get("compiled") else 2,
                    errors if near_complete else holes if a.get("compiled") else errors,
                    -a.get("round", 0))
        return sorted(cands, key=key)[:k]

    def _repair_context(self, attempts: list[dict], k: int = 2) -> str:
        best = self._best_partials(attempts, k)
        if not best:
            return ""
        parts = ["REPAIR CONTEXT — the most promising failed attempts so far, with the compiler's exact complaints. "
                 "Prefer FIXING one of these over starting from scratch when the plan was sound:"]
        for a in best:
            status = (f"compiles but leaves {a['n_sorries']} `sorry`" if a.get("compiled")
                      else f"{len(a['errors'])} compiler error(s)")
            parts.append(f"--- {a['name']} [{a['plan'][:120]}] — {status}\n```lean\n{a['code']}\n```\n"
                         "Compiler output:\n" + "\n".join("  " + e for e in a["errors"][:8]))
        return "\n".join(parts)

    def _record(self, attempts, name, plan, rnd, block, res, extra: dict | None = None):
        rec = {"name": name, "plan": plan, "round": rnd, "errors": res["errors"][:8] + res.get("notes", [])[:4],
               "timeout": res.get("timeout", False), "compiled": bool(res["ok"]),
               "n_sorries": hole_count(block) if res["ok"] else None,
               "code": block}
        if extra:
            rec.update(extra)   # e.g. sandbox dir + final summary of the agentic session that produced it
        attempts.append(rec)
        return rec

    def _screen(self, attempts, name, plan, rnd, block, frozen) -> bool:
        """Pre-compile checks; returns True if the block may be compiled."""
        if not contains_frozen(block, frozen):
            attempts.append({"name": name, "plan": plan, "round": rnd, "rejected": True,
                             "errors": ["attempt altered the frozen theorem statement — rejected without compiling"]})
            self.log.event("prove", "frozen_violation", name=name)
            return False
        # Compile partial proofs so decomposition can reuse checked progress.
        # Success still requires no sorry and a clean final axiom audit.
        banned = has_banned(block, allow_sorry=True)
        if banned:
            attempts.append({"name": name, "plan": plan, "round": rnd, "rejected": True,
                             "errors": [f"used banned construct `{banned}` — rejected"]})
            self.log.event("prove", "banned", name=name, construct=banned)
            return False
        return True

    def _verified_block(self) -> str:
        """Verify every Mathlib-looking name the literature stage mentioned, once per run."""
        if "verified_names" not in self.state:
            names = candidate_names(self.state.get("literature", "") + "\n" + self.problem.get("notes", ""))
            self.state["verified_names"] = verify_names(names) if names else ""
            self.save()
        return self.state["verified_names"]

    def _sandbox(self, name: str, seed_body: str, seed_dir: str | Path | None = None) -> Path:
        sb = self.run_dir / "sandbox" / name
        sb.mkdir(parents=True, exist_ok=True)
        if seed_dir and Path(seed_dir).is_dir() and Path(seed_dir) != sb:
            # persistent workspace: the next session continues from the previous one's files (scratch lemmas too)
            for f in Path(seed_dir).iterdir():
                if f.is_file() and f.name not in ("TASK.md", "check.sh", "SUMMARY.md"):
                    shutil.copy(f, sb / f.name)
        (sb / "Attempt.lean").write_text(compose(seed_body, self.imports))
        (sb / "check.sh").write_text(f"""#!/bin/bash
# Compile a Lean file against the harness's Mathlib project. Usage: ./check.sh Attempt.lean
F="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
cd "{FORMAL}" || exit 1
perl -e 'alarm shift; exec @ARGV' {self.args.lean_timeout} lake env lean "$F" 2>&1 | head -150
echo "exit=${{PIPESTATUS[0]}}"
""")
        os.chmod(sb / "check.sh", 0o755)
        return sb

    def _agentic_attempt(self, name: str, seed_body: str, prompt: str, seed_dir=None, model: str | None = None
                         ) -> tuple[str, str, str]:
        """Run one sandboxed agentic attempt; returns (response_text, final Attempt.lean body, sandbox dir)."""
        sb = self._sandbox(name, seed_body, seed_dir)
        (sb / "TASK.md").write_text(prompt)
        try:
            if hasattr(self.llm, "complete_agentic"):
                if model and hasattr(self.llm, "model"):
                    # ensemble: a per-attempt model override (backend objects are cheap; keep accounting on self.llm)
                    alt = ClaudeCliBackend(model, self.llm.timeout, self.llm.call_budget_usd)
                    text = alt.complete_agentic("prove-agentic", prompt, sb, self.args.agentic_turns)
                    with self.llm._lock:
                        self.llm.total_cost_usd += alt.total_cost_usd
                        for k, v in alt.total_tokens.items():
                            self.llm.total_tokens[k] = self.llm.total_tokens.get(k, 0) + v
                        self.llm.last_meta = alt.last_meta
                else:
                    text = self.llm.complete_agentic("prove-agentic", prompt, sb, self.args.agentic_turns)
            else:
                text = self.llm.complete("prove-agentic", prompt)
        except (RuntimeError, subprocess.TimeoutExpired) as e:
            if ClaudeCliBackend.HARD_RE.search(str(e)):
                raise   # spend/usage limit, auth: infrastructure failure — stop the run (it is resumable)
            # Running out of turns/budget/time is a FAILED ATTEMPT, not a fatal run error: the sandbox file
            # is still harvested below (it often already holds a compiling proof the model did not report).
            text = ""
            self.log.event("llm", "error", purpose="prove-agentic", name=name, error=repr(e)[:300])
        meta = getattr(self.llm, "last_meta", {}) or {}
        self.log.event("llm", "response", purpose="prove-agentic", name=name, chars=len(text),
                       cost_usd=meta.get("cost_usd"), turns=meta.get("turns"), tokens=meta.get("tokens"))
        (self.run_dir / "transcripts").mkdir(exist_ok=True)
        n = len(list((self.run_dir / "transcripts").glob("*.md"))) + 1
        (self.run_dir / "transcripts" / f"{n:03d}-prove-agentic.md").write_text(
            f"# prove-agentic {name}\n\n## prompt\n\n{prompt}\n\n## response\n\n{text}\n")
        try:
            final_file = strip_imports((sb / "Attempt.lean").read_text())
            final_file = "\n".join(f"-- IMPORTS: {m}" for m in import_lines((sb / "Attempt.lean").read_text())) + "\n" + final_file
        except OSError:
            final_file = ""
        (sb / "SUMMARY.md").write_text(text[-2500:])
        return text, final_file, str(sb)

    def _round_models(self, rnd: int, samples: int) -> list:
        """Ensemble plan diversity: from round 2 on, rotate through --models across the agentic attempts."""
        models = [m for m in (getattr(self.args, "models", None) or "").split(",") if m.strip()]
        if rnd < 2 or not models:
            return [None] * samples
        return [models[(i + rnd) % len(models)] for i in range(samples)]

    def _critic(self, attempts: list, rnd: int) -> str:
        """Cheap review of the failed plans before an agentic session starts (cached per round)."""
        key = f"critic_r{rnd}"
        if key in self.state:
            return self.state[key]
        digest = self._history_digest(attempts, cap=6) + "\n\n" + self._repair_context(attempts, 1)[:6000]
        try:
            resp = self.ask("critic", CRITIC_PROMPT.format(statement=self.state["statement"], digest=digest))
        except Harness.BudgetExhausted:
            raise
        except RuntimeError as e:
            if ClaudeCliBackend.HARD_RE.search(str(e)):
                raise
            resp = ""
        text = ("CRITIC NOTES (a reviewer's reading of the failed attempts; weigh, don't obey):\n" + resp.strip()[:3000]) if resp.strip() else ""
        self.state[key] = text
        self.save()
        return text

    def search_block(self) -> str:
        s = self.state.get("search") or {}
        if s.get("status") == "found":
            if s.get("kind") == "witness":
                return ("SEARCH RESULT — a bounded computation found a WITNESS for the existential statement:\n"
                        f"  {json.dumps(s.get('witness'))}\n"
                        "Certify it: instantiate the existential with exactly these values and close the remaining goals with "
                        "`norm_num [Nat.factorial]`, `decide +kernel` (finite checks) or `simp`; keep large numbers in factored "
                        "form if exponent arithmetic is involved; never use `native_decide`.")
            return ("SEARCH RESULT — a bounded computation found a COUNTEREXAMPLE to the (universal) frozen statement:\n"
                    f"  {json.dumps(s.get('witness'))}\n"
                    "The frozen statement is therefore FALSE as stated; do not try to prove it. (In --open mode this witness "
                    "proves the negation direction.)")
        return ""

    def stage_prove(self) -> bool:
        if self.state.get("proof"):
            return True
        statement = self.state["statement"]
        frozen = statement_prefix(statement)
        attempts = self.state.get("attempts", [])
        retrieval = merge_retrieval(self.state.get("proof_retrieval", []), self.initial_retrieval())
        verified = self._verified_block()
        playbook = self.playbook_block()
        literature = self.state.get("literature", "")
        force_agentic = self.state.get("force_agentic", False)
        for rnd in range(1, self.args.rounds + 1):
            repair = self._repair_context(attempts)
            agentic = (self.args.agentic != "off") and (force_agentic or rnd > self.args.agentic_after
                                                        or self.args.agentic == "always")
            cands: list[tuple[str, str, str]] = []   # (name, plan, block)
            sandbox_meta: dict = {}                  # attempt name -> {"sandbox": dir, "summary": text}
            if not agentic:
                try:
                    resp = self.ask("prove", prove_prompt(
                        self.problem, statement, literature, retrieval, self._history_digest(attempts),
                        rnd, self.args.samples, self.imports, repair=repair, verified=verified, playbook=playbook))
                except RuntimeError as e:
                    if not re.search(r"budget", str(e), re.I):
                        raise   # spend limits, auth, network: infrastructure failure, stop (resumable)
                    # A one-shot call that thinks past its per-call budget produces nothing. That is a FAILED
                    # ATTEMPT (the problem is hard for one-shot generation), so escalate to compiler-in-the-loop
                    # attempts for the remaining rounds instead of aborting the run.
                    meta = getattr(self.llm, "last_meta", {}) or {}
                    self.log.event("prove", "budget_exceeded", round=rnd, cost_usd=meta.get("cost_usd"), error=str(e)[:200])
                    self.log.event("llm", "response", purpose="prove", chars=0, cost_usd=meta.get("cost_usd"), error="budget")
                    attempts.append({"name": f"proof-r{rnd}-oneshot", "plan": "one-shot generation", "round": rnd,
                                     "rejected": True, "errors": [f"the one-shot call exceeded its ${self.args.call_budget} "
                                     "budget before finishing (escalating to compiler-in-the-loop attempts)"]})
                    force_agentic = self.state["force_agentic"] = True
                    self.state["attempts"] = attempts
                    self.save()
                    continue
                plans = re.findall(r"^ATTEMPT\s+\d+:\s*(.+)$", resp, re.M)
                blocks = lean_blocks(resp)
                retrieval = merge_retrieval(retrieval, run_retrieval_directives(resp))
                self.state["proof_retrieval"] = retrieval
                self.save()
                for i, block in enumerate(blocks):
                    cands.append((f"proof-r{rnd}-a{i}", plans[i] if i < len(plans) else "?", block))
            else:
                samples = self.args.agentic_samples
                self.log.event("prove", "agentic_round", round=rnd, samples=samples)
                seeds = self._best_partials(attempts, samples)
                # persistent workspace: continue from the best previous agentic session (files + its final summary)
                prev = [a for a in seeds if a.get("sandbox")]
                seed_dir = prev[0]["sandbox"] if prev else None
                previous = prev[0].get("summary", "") if prev else ""
                seed_bodies = [a["code"] for a in seeds] or [statement]
                critic = self._critic(attempts, rnd) if (rnd > 1 and attempts) else ""
                models = self._round_models(rnd, samples)
                prompt = agentic_prompt(self.problem, statement, literature, repair, verified,
                                        self.imports, self.args.agentic_turns, playbook, tool_backend=self.args.backend,
                                        previous=previous, critic=critic, search=self.search_block())
                jobs = [(f"proof-r{rnd}-g{i}", seed_bodies[i % len(seed_bodies)], models[i]) for i in range(samples)]
                self.log.event("llm", "request", purpose="prove-agentic", n=len(jobs), chars=len(prompt),
                               models=[m or "default" for m in models], seed_dir=seed_dir)
                with ThreadPoolExecutor(max_workers=max(1, min(len(jobs), COMPILE_WORKERS))) as ex:
                    outs = list(ex.map(lambda j: self._agentic_attempt(j[0], j[1], prompt, seed_dir=seed_dir, model=j[2]), jobs))
                self._check_run_budget("prove-agentic")
                for (name, _, model), (text, final_file, sb) in zip(jobs, outs):
                    blocks = lean_blocks(text)
                    m = re.search(r"^RESULT:\s*(\S+)", text, re.M)
                    plan = f"agentic ({m.group(1) if m else 'no RESULT line'}; model={model or 'default'})"
                    sandbox_meta[name] = sandbox_meta[name + "-file"] = {"sandbox": sb, "summary": text[-1500:]}
                    if blocks:
                        cands.append((name, plan, blocks[-1]))
                    if final_file and (not blocks or norm_ws(strip_comment_lines(final_file)) != norm_ws(strip_comment_lines(blocks[-1]))):
                        cands.append((name + "-file", plan + " [sandbox file]", final_file))
            # cheap pre-screen, then compile survivors in parallel
            to_compile = [(n, p, b) for (n, p, b) in cands if self._screen(attempts, n, p, rnd, b, frozen)]
            if to_compile:
                with ThreadPoolExecutor(max_workers=COMPILE_WORKERS) as ex:
                    results = list(ex.map(lambda t: self.check(t[2], t[0]), to_compile))
                for (name, plan, block), res in zip(to_compile, results):
                    if res["ok"] and not res["sorries"] and "proof" not in self.state:
                        self._record(attempts, name, plan, rnd, res.get("body", block), res, sandbox_meta.get(name))
                        self.state["proof"] = res.get("body", block)
                        self.state["attempts"] = attempts
                        self.save()
                        self.log.event("prove", "SUCCESS", name=name, round=rnd, agentic=agentic)
                        return True
                    if not (res["ok"] and not res["sorries"]):
                        self._record(attempts, name, plan, rnd, res.get("body", block), res, sandbox_meta.get(name))
                        # feed Try-this suggestions from exact?/apply? into next round's retrieval
                        tries = [x for x in res["infos"] if "Try this" in x]
                        if tries:
                            retrieval = (retrieval + [f"suggestion from {name}: {t}" for t in tries])[-20:]
                        # verify any names the failed attempt used that the compiler did not know
                        unknown = unknown_names_from_errors(res["errors"])
                        if unknown:
                            retrieval = (retrieval + [verify_names(unknown[:8])])[-20:]
            self.state["attempts"] = attempts
            self.state["proof_retrieval"] = merge_retrieval([], retrieval)
            self.save()
        return False

    def stage_decompose(self) -> bool:
        statement = self.state["statement"]
        frozen = statement_prefix(statement)
        history = self._history_digest(self.state.get("attempts", []))
        skeleton = self.state.get("decomposition", {}).get("code")
        if skeleton and not contains_frozen(skeleton, frozen):
            skeleton = None
        # Seed from the best compiling-with-sorries prove attempt: it already IS a lemma skeleton.
        ranked = self._best_partials(self.state.get("attempts", []), len(self.state.get("attempts", [])))
        seeds = [a for a in ranked if a.get("compiled")]
        repair_seed = next((a for a in ranked if not a.get("compiled") and
                            hole_count(a["code"]) == 0 and 0 < len(a.get("errors", [])) <= 4 and
                            contains_frozen(a["code"], frozen) and not has_banned(a["code"])), None)
        if not skeleton and seeds and contains_frozen(seeds[0]["code"], frozen):
            skeleton = seeds[0]["code"]
            self.log.event("decompose", "seeded_from_attempt", name=seeds[0]["name"], sorries=seeds[0]["n_sorries"])
        if not skeleton and repair_seed:
            # The frozen formalization is already a compiling fallback. Do not
            # spend an outline-generation call before repairing a complete file.
            skeleton = statement
        for attempt in range(1, 4):
            if skeleton:
                break
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
        self.log.event("decompose", "skeleton_accepted", sorries=hole_count(skeleton))
        # Free specialists first: Lean's own tactics (and an optional external subgoal prover) on every hole,
        # before any model call. Runs again whenever the working skeleton changes.
        skeleton = self._close_holes_without_model(skeleton, frozen)
        if hole_count(skeleton) == 0 and not has_banned(skeleton):
            final = self.check(skeleton, "assembled-cascade")
            if final["ok"] and not final["sorries"]:
                self.state["proof"] = skeleton
                self.save()
                self.log.event("decompose", "SUCCESS", by="specialist-cascade")
                return True

        checkpoint = self.state.get("decomposition", {})
        current = skeleton
        working = checkpoint.get("candidate", repair_seed["code"] if repair_seed else current)
        if not contains_frozen(working, frozen) or has_banned(working, allow_sorry=True):
            working = current
        budget = self.args.decompose_rounds
        retrieval: list[str] = merge_retrieval(self.state.get("proof_retrieval", []), checkpoint.get("retrieval", []))
        last_errors: list[str] = checkpoint.get("errors", repair_seed["errors"] if repair_seed else []) if working != current else []
        unknown = unknown_names_from_errors(last_errors)
        if unknown:
            retrieval = merge_retrieval(retrieval, [verify_names(unknown[:8])])
        offset = checkpoint.get("rounds_used", 0)
        def checkpoint_repair():
            self.state["decomposition"] = {
                "code": current, "candidate": working, "errors": last_errors,
                "retrieval": retrieval, "rounds_used": offset + self.args.decompose_rounds - budget,
            }
            self.save()
        checkpoint_repair()
        cascaded = {hashlib.sha256(skeleton.encode()).hexdigest()}
        while budget > 0 and (hole_count(current) or last_errors):
            if hole_count(current) and not last_errors:
                h = hashlib.sha256(current.encode()).hexdigest()
                if h not in cascaded:
                    cascaded.add(h)
                    current = self._close_holes_without_model(current, frozen)
                    working = current
                    checkpoint_repair()
                    if hole_count(current) == 0:
                        break
            budget -= 1
            resp = self.ask("refine", refine_prompt(self.problem, working, last_errors,
                                                    self.state.get("literature", ""), retrieval,
                                                    self.imports))
            blocks = lean_blocks(resp)
            retrieval = merge_retrieval(retrieval, run_retrieval_directives(resp))
            if not blocks:
                checkpoint_repair()
                continue
            cand = max(blocks, key=len)
            if not contains_frozen(cand, frozen) or has_banned(cand, allow_sorry=True):
                # Keep diagnostics paired with the unchanged working candidate.
                checkpoint_repair()
                continue
            res = self.check(cand, f"refine-{offset + self.args.decompose_rounds - budget}")
            cand = res.get("body", cand)
            working = cand
            if res["ok"] and hole_count(cand) < hole_count(current):
                current = cand
                last_errors = []
                self.log.event("decompose", "progress", sorries_left=hole_count(cand))
            elif res["ok"]:
                working = current
                last_errors = []
            else:
                last_errors = res["errors"] or [res.get("raw", "")[-8000:] or "Compilation failed without diagnostics"]
                unknown = unknown_names_from_errors(last_errors)
                if unknown:
                    retrieval = merge_retrieval(retrieval, [verify_names(unknown[:8])])
                suggestions = [x for x in res.get("infos", []) if "Try this" in x]
                retrieval = merge_retrieval(retrieval, suggestions)
            checkpoint_repair()
        if not hole_count(current) and not has_banned(current):
            final = self.check(current, "assembled")
            if final["ok"] and not final["sorries"]:
                self.state["proof"] = current
                self.save()
                self.log.event("decompose", "SUCCESS")
                return True
        return False

    # -- specialist cascade: close `sorry` holes with Lean's own tactics (free) or an external prover ----------

    CASCADE = "first | omega | (simp_all) | positivity | (norm_num) | (nlinarith) | (decide +kernel) | (aesop)"

    @staticmethod
    def _hole_spans(code: str) -> list[tuple[int, int, bool]]:
        """(start, end, tactic_position) for every `sorry` token outside comments."""
        spans, i, n = [], 0, len(code)
        depth = 0
        while i < n:
            if code.startswith("/-", i):
                depth += 1; i += 2; continue
            if depth and code.startswith("-/", i):
                depth -= 1; i += 2; continue
            if depth:
                i += 1; continue
            if code.startswith("--", i):
                j = code.find("\n", i); i = n if j == -1 else j; continue
            m = re.match(r"\bsorry\b", code[i:])
            if m and (i == 0 or not (code[i - 1].isalnum() or code[i - 1] in "_.'")):
                line_start = code.rfind("\n", 0, i) + 1
                before = code[line_start:i].rstrip()
                tactic_pos = before == "" or before.endswith("by") or before.endswith("=>") or before.endswith("·") or before.endswith("<;>")
                spans.append((i, i + 5, tactic_pos)); i += 5; continue
            i += 1
        return spans

    def _substitute(self, code: str, spans, texts: dict) -> str:
        out, last = [], 0
        for k, (s, e, _) in enumerate(spans):
            out.append(code[last:s]); out.append(texts.get(k, "sorry")); last = e
        out.append(code[last:])
        return "".join(out)

    def _close_holes_without_model(self, code: str, frozen: str) -> str:
        """Try the specialist cascade on every hole at once, then `exact?` on the survivors, then the optional
        external subgoal prover. Each pass is one Lean compile; closed holes are kept, others revert to `sorry`.
        Logs which component closed each hole."""
        spans = self._hole_spans(code)
        if not spans or getattr(self.args, "no_cascade", False):
            return code
        lines_of = [code.count("\n", 0, s) + 1 for s, _, _ in spans]
        # pass 1: tactic cascade
        texts = {k: (self.CASCADE if tac else f"(by {self.CASCADE})") for k, (_, _, tac) in enumerate(spans)}
        cand = self._substitute(code, spans, texts)
        res = self.check(cand, "cascade")
        bad_lines = {int(m.group(1)) for e in res["errors"] for m in [re.match(r"line (\d+):", e)] if m}
        closed = {}
        if not res.get("timeout"):
            for k, ln in enumerate(lines_of):
                if ln not in bad_lines and (res["ok"] or True):
                    closed[k] = ("cascade", texts[k])
        # a hole whose line has no error is closed only if the whole file compiled or its line is error-free;
        # if the file failed for other reasons keep only those and revert the rest
        keep = {k: v[1] for k, v in closed.items()}
        code2 = self._substitute(code, spans, keep)
        if keep:
            res2 = self.check(code2, "cascade-keep")
            if not res2["ok"]:
                keep, code2 = {}, code   # conservative: something interacted badly, revert everything
                closed = {}
        for k in closed:
            self.log.event("decompose", "hole_closed", hole=k, line=lines_of[k], by="specialist-cascade")
        # pass 2: exact? on the survivors
        spans2 = self._hole_spans(code2)
        if spans2:
            lines2 = [code2.count("\n", 0, s) + 1 for s, _, _ in spans2]
            texts2 = {k: ("exact?" if tac else "(by exact?)") for k, (_, _, tac) in enumerate(spans2)}
            res = self.check(self._substitute(code2, spans2, texts2), "cascade-exact")
            found = {}
            for info in res["infos"]:
                m = re.match(r"line (\d+):\d+: Try this: (.*)", info, re.S)
                if m:
                    ln = int(m.group(1)); sugg = m.group(2).strip().splitlines()[0].strip()
                    for k, l2 in enumerate(lines2):
                        if l2 == ln:
                            found[k] = sugg if spans2[k][2] else f"(by {sugg})"
            if found:
                code3 = self._substitute(code2, spans2, found)
                res3 = self.check(code3, "cascade-exact-keep")
                if res3["ok"]:
                    for k in found:
                        self.log.event("decompose", "hole_closed", hole=k, line=lines2[k], by="exact?", suggestion=found[k][:120])
                    code2 = code3
        # pass 3: optional external subgoal prover on whatever remains
        spec = getattr(self.args, "subgoal_prover", None)
        spans3 = self._hole_spans(code2)
        if spec and spans3:
            code2 = self._external_subgoals(code2, spans3, spec)
        return code2

    def _extract_goals(self, code: str, spans) -> dict:
        """Goal text for each hole via `done` substitution (Lean reports `unsolved goals <goal>` at the hole's line)."""
        lines_of = [code.count("\n", 0, s) + 1 for s, _, _ in spans]
        res = self.check(self._substitute(code, spans, {k: ("done" if tac else "(by done)") for k, (_, _, tac) in enumerate(spans)}), "goals")
        goals = {}
        for e in res["errors"]:
            m = re.match(r"line (\d+):\d+: unsolved goals\n(.*)", e, re.S)
            if m:
                ln = int(m.group(1))
                for k, l2 in enumerate(lines_of):
                    if l2 == ln:
                        goals[k] = m.group(2).strip()
        return goals

    def _external_subgoals(self, code: str, spans, spec: str) -> str:
        """Pluggable prover: `module:function` with signature prove(goal: str, timeout: int) -> str | None (a tactic proof)."""
        try:
            import importlib
            modname, fn = spec.split(":")
            prove = getattr(importlib.import_module(modname), fn)
        except Exception as e:   # noqa: BLE001
            self.log.event("decompose", "subgoal_prover_unavailable", error=repr(e)[:200])
            return code
        goals = self._extract_goals(code, spans)
        texts = {}
        for k, goal in goals.items():
            try:
                proof = prove(goal, 120)
            except Exception as e:   # noqa: BLE001
                self.log.event("decompose", "subgoal_prover_error", hole=k, error=repr(e)[:200])
                continue
            if proof and not has_banned(proof):
                texts[k] = proof if spans[k][2] else f"(by {proof})"
        if not texts:
            return code
        cand = self._substitute(code, spans, texts)
        res = self.check(cand, "subgoal-prover")
        if res["ok"] and hole_count(cand) < hole_count(code):
            for k in texts:
                self.log.event("decompose", "hole_closed", hole=k, by=f"subgoal-prover:{spec}")
            return cand
        return code

    def stage_verify(self) -> dict:
        # Deliberately NOT short-circuited on resume: a saved `verify.all_clear` is never trusted; the mechanical
        # guard (compile, sorry, banned, frozen, axioms) always re-runs (tests/test_outcomes.py pins this).
        proof = self.state["proof"]
        self.state.pop("verify", None)
        self.save()  # Interrupted re-verification must not retain a stale success.
        thm = getattr(self, "thm_name", f"erdos_{self.problem['id']}")
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
        banned = has_banned(proof)
        frozen_match = contains_frozen(proof, statement_prefix(self.state["statement"]))
        clean = res["ok"] and not res["sorries"] and axioms <= STD_AXIOMS and bool(axline) and not banned and frozen_match

        if clean and getattr(self, "direction", None) == "program":
            # research-program sub-statement: it is a lemma, never claimed to be the problem, so the semantic judge
            # (which compares against the ORIGINAL problem) does not apply; mechanical verification is the whole bar.
            back = ""
            faithful = {"faithful": True, "issues": ["sub-goal of a research program: faithfulness judge not applicable"],
                        "verdict": "mechanically verified lemma (not a resolution of the problem)"}
        elif clean and getattr(self, "direction", None) in ("pos", "neg"):
            back = self.ask("backtranslate", backtranslate_prompt(self.state["statement"])).strip()
            cmp_resp = self.ask("faithful", compare_prompt(self.problem, back, direction=self.direction))
            faithful = json_block(cmp_resp) or {"faithful": None, "issues": ["judge returned no JSON"]}
        elif clean:
            back = self.ask("backtranslate", backtranslate_prompt(self.state["statement"])).strip()
            cmp_resp = self.ask("faithful", compare_prompt(self.problem, back))
            faithful = json_block(cmp_resp) or {"faithful": None, "issues": ["judge returned no JSON"]}
        else:
            back = ""
            faithful = {"faithful": False, "issues": ["mechanical verification failed; semantic judge skipped"]}

        verdict = {
            "compiles": res["ok"], "sorry_free": not res["sorries"],
            "banned": banned, "frozen_match": frozen_match,
            "axioms": sorted(axioms), "axioms_clean": axioms <= STD_AXIOMS,
            "backtranslation": back, "faithful": faithful, "all_clear": clean and faithful.get("faithful") is True,
        }
        self.state['direction'] = getattr(self, 'direction', self.state.get('direction'))
        verdict['artifact_sha256'] = fingerprint(self.problem, self.state, getattr(self, 'imports', []), environment_snapshot(FORMAL))
        self.state["verify"] = verdict
        self.save()
        self.log.event("verify", "done", **{k: v for k, v in verdict.items() if k != "backtranslation"})
        if clean:
            out = self.run_dir / "final" / f"Erdos{self.problem['id']}.lean"
            out.parent.mkdir(exist_ok=True)
            out.write_text(compose(proof, self.imports))
            if verdict["all_clear"] and not getattr(self, "direction", None) and not self.problem.get("open"):
                # feed the knowledge base: the verified proof becomes a regression case and a lemma source
                # (open-problem directions are reported under knowledge/open/, never as regression cases)
                solved = KNOWLEDGE / "solved"
                solved.mkdir(parents=True, exist_ok=True)
                (solved / f"Erdos{self.problem['id']}.lean").write_text(compose(proof, self.imports))
                (solved / f"Erdos{self.problem['id']}.json").write_text(json.dumps({
                    "problem": self.problem["id"], "run": self.run_dir.name, "imports": self.imports,
                    "statement": self.state["statement"], "verified_at": now()}, indent=2))
                n = harvest_lemmas(proof, self.problem["id"], self.run_dir.name)
                self.log.event("knowledge", "harvested", lemmas=n)
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
        cost = sum(float(e.get("cost_usd") or 0) for e in events if e.get("event") == "response")
        cost_known = all(e.get("cost_usd") is not None for e in events if e.get("event") == "response")
        cost_label = f"${cost:.2f}" if cost_known else f"unavailable (reported subtotal ${cost:.2f})"
        llm_calls = sum(1 for e in events if e.get("event") == "response")
        llm_secs = sum(float(e.get("secs") or 0) for e in events if e.get("event") == "response")
        wall = None
        try:
            ts = [datetime.strptime(e["ts"], "%Y-%m-%dT%H:%M:%SZ") for e in events if e.get("event") in ("start", "end") and e.get("stage") == "run"]
            if len(ts) >= 2:
                wall = round((max(ts) - min(ts)).total_seconds() / 60, 1)
        except Exception:
            pass
        auto_imps = self.state.get("auto_imports", [])
        lines = [
            f"# Harness run report — Erdős problem #{self.problem['id']}",
            "",
            f"- **Status:** {'FORMAL PROOF VERIFIED — mathematical review tracked separately' if proved and v.get('all_clear') else 'PROVED (verification caveats — see below)' if proved else 'NOT PROVED (out of budget)'}",
            f"- **Review milestone:** {self.state.get('solution_review', {}).get('stage', 'not assessed')}",
            f"- **Resolution claim eligible:** {self.state.get('solution_review', {}).get('resolution_claim_eligible', False)}",
            f"- **Pending independent evidence:** {', '.join(self.state.get('solution_review', {}).get('pending', []))}",
            f"- **Problem:** {self.problem['statement']}",
            f"- **Source:** {self.problem.get('url', '')}",
            f"- **Lean checks run:** {n_checks}; proof attempts: {n_attempts}",
            f"- **LLM calls:** {llm_calls}; LLM time: {round(llm_secs / 60, 1)} min; cost: {cost_label}; wall-clock: {wall} min",
            f"- **Imports:** {', '.join(self.imports)}" + (f" (auto-added: {', '.join(auto_imps)})" if auto_imps else ""),
            "",
            f"- **Outcome:** {self.state.get('outcome', 'proved' if proved else 'not proved')}"
            + (f" — stopped because: {self.state['stop_reason']}" if self.state.get("stop_reason") and not proved else ""),
            f"- **Triage:** mode=`{self.state.get('mode', 'fast')}` — {self.state.get('mode_reason', 'no assessment')}"
            + (f"; assessment: shape={self.state['assessment'].get('shape')}, status={self.state['assessment'].get('status')}, "
               f"depth={self.state['assessment'].get('depth')}, computable={self.state['assessment'].get('computable')}, "
               f"tier={self.state['assessment'].get('budget_tier')}, known_bound={self.state['assessment'].get('known_bound')}"
               if self.state.get("assessment") else ""),
            f"- **Search:** {json.dumps(self.state.get('search'))[:400]}" if self.state.get("search") else "- **Search:** not run",
            f"- **Partial results:** {self.state['partial']}" if self.state.get("partial") else "",
            f"- **Tokens:** " + json.dumps({k: sum(int((json.loads(l).get('tokens') or {}).get(k) or 0) for l in open(self.log.path) if '\"response\"' in l) for k in ('in', 'out', 'cache_read', 'cache_write')}),
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
        proved, outcome = False, "not_proved"
        try:
            try:
                self.stage_literature()
                if getattr(self.args, "open", False):
                    return self.run_open()
                self.stage_formalize()
                self.stage_assess()
                if getattr(self.args, "stop_after", None) == "assess":
                    self.report(False)
                    self.log.event("run", "end", stopped_after="assess", mode=self.state.get("mode"))
                    return 0
                if self.state.get("mode") == "construct":
                    self.stage_construct()
                    if getattr(self.args, "stop_after", None) == "construct":
                        c = self.state.get("construct", {})
                        self.state["outcome"] = "construct:" + str(c.get("status"))
                        self.report(False)
                        self.log.event("run", "end", stopped_after="construct", status=c.get("status"), spent_usd=round(self.spent_usd(), 2))
                        return 3 if c.get("status") == "certified" else 2
                if self.state.get("mode") == "research":
                    return self.run_program()
                self.stage_search()
                if getattr(self.args, "stop_after", None) == "search":
                    self.report(False)
                    self.log.event("run", "end", stopped_after="search", search=self.state.get("search", {}).get("status"))
                    return 0
                proved = bool(self.state.get("proof")) if self.state.get("decomposition") else self.stage_prove()
                if not proved:
                    self.log.event("run", "escalating_to_decompose")
                    proved = self.stage_decompose()
            except Harness.BudgetExhausted as e:
                self.log.event("run", "stopped_on_budget", detail=str(e))
                outcome = "budget_exhausted"
                self.state["stop_reason"] = f"run budget exhausted after {self.state.get('mode', 'fast')} mode: {e}"
            if proved:
                self.stage_verify()
                outcome = "proved" if self.state.get("verify", {}).get("all_clear") is True else "proved_unverified"
                if outcome == "proved_unverified":
                    self.state["stop_reason"] = "proof compiled but final verification (axioms/frozen/faithfulness) did not clear"
            else:
                if outcome != "budget_exhausted":
                    n_att = len(self.state.get("attempts", []))
                    self.state["stop_reason"] = (f"mode={self.state.get('mode', 'fast')}: {self.args.rounds} proof round(s) "
                                                 f"({n_att} attempts) and {self.args.decompose_rounds} refinement round(s) exhausted without a sorry-free proof"
                                                 + ("; search found nothing" if (self.state.get('search') or {}).get('status') == 'none' else ""))
                if self.stage_partial():
                    outcome = "partial" if outcome != "budget_exhausted" else "budget_exhausted+partial"
            self.state["outcome"] = outcome
            self.save()
            self.report(proved)
            self.log.event("run", "end", proved=proved, outcome=outcome,
                           all_clear=self.state.get("verify", {}).get("all_clear"),
                           spent_usd=round(self.spent_usd(), 2))
            (self.run_dir / "DONE").write_text(json.dumps(
                {"proved": proved, "outcome": outcome, "verify": self.state.get("verify", {}).get("all_clear"), "solution_review": self.state.get("solution_review", {})}))
            # exit codes: 0 proved+verified · 3 partial results only · 2 not proved (incl. budget stop) · 1 infrastructure error
            return 0 if outcome == "proved" else 3 if "partial" in outcome else 2
        except BaseException as e:
            self.log.event("run", "fatal", error=repr(e)[:500])
            (self.run_dir / "DONE").write_text(json.dumps({"proved": False, "fatal": repr(e)[:200]}))
            raise

    # -- triage (assess) -------------------------------------------------------------------------

    def stage_assess(self):
        """Medium-effort, $1-capped classification of the frozen target; the routing decision is logged."""
        if "mode" in self.state:
            return
        if getattr(self.args, "skip_assess", False) or not self.state.get("statement"):
            reason = "--skip-assess" if getattr(self.args, "skip_assess", False) else "no frozen statement to assess"
            self.state["assessment"], self.state["mode"], self.state["mode_reason"] = {}, "fast", reason
            self.save()
            return
        resp = self.ask("assess", ASSESS_PROMPT.format(
            pid=self.problem["id"], status=self.problem.get("status", "unknown"), statement_en=self.problem["statement"],
            notes=(self.problem.get("notes") or "(none)")[:3000], literature=(self.state.get("literature") or "(none)")[:5000],
            statement=self.state["statement"]))
        a = json_block(resp) or {}
        mode, reason = decide_mode(a, self.args, self.problem)
        self.state["assessment"], self.state["mode"], self.state["mode_reason"] = a, mode, reason
        self.save()
        self.log.event("assess", "routed", mode=mode, reason=reason, shape=a.get("shape"), status=a.get("status"),
                       depth=a.get("depth"), computable=a.get("computable"), tier=a.get("budget_tier"))

    # -- computational search (witness / counterexample) -----------------------------------------

    def stage_search(self):
        """Model-written bounded Python search for a witness (∃-shaped target) or counterexample (∀-shaped),
        executed under a static safety scan + timeout; hits are logged and later certified in Lean."""
        if "search" in self.state:
            return
        pol = getattr(self.args, "search", "auto")
        if pol == "off" or (pol == "auto" and self.state.get("mode") != "search-first"):
            self.state["search"] = {"status": "skipped", "reason": f"policy={pol} mode={self.state.get('mode')}"}
            self.save()
            return
        kind = statement_shape(self.state["statement"])
        if kind is None:
            self.state["search"] = {"status": "skipped", "reason": "statement shape not ∃/∀"}
            self.save()
            return
        cap_s = int(getattr(self.args, "search_seconds", 90))
        kind_expl = ("concrete values for the existentially quantified variables making the statement true"
                     if kind == "witness" else
                     "concrete values for the universally quantified variables making the statement FALSE")
        resp = self.ask("search", SEARCH_PROMPT.format(
            kind=kind, pid=self.problem["id"], statement_en=self.problem["statement"],
            notes=(self.problem.get("notes") or "(none)")[:2500], statement=self.state["statement"],
            cap_seconds=cap_s, cap_candidates="10^7", kind_expl=kind_expl))
        m = re.search(r"```python\s*\n(.*?)```", resp, re.S)
        sdir = self.run_dir / "search"
        sdir.mkdir(exist_ok=True)
        result = {"status": "error", "kind": kind}
        code = m.group(1) if m else ""
        bad = unsafe_python(code) if code else "no python block"
        if bad and bad != "no python block":
            # one retry naming the rejected construct (the allowlist is stdlib-only, no I/O)
            resp = self.ask("search", SEARCH_PROMPT.format(
                kind=kind, pid=self.problem["id"], statement_en=self.problem["statement"],
                notes=(self.problem.get("notes") or "(none)")[:2500], statement=self.state["statement"],
                cap_seconds=cap_s, cap_candidates="10^7", kind_expl=kind_expl)
                + f"\n\nYour previous script was REJECTED by the safety screen for `{bad}`. Use only the allowed modules "
                  f"({', '.join(sorted(ALLOWED_PY_MODULES))}) and no file/network/OS access.")
            m = re.search(r"```python\s*\n(.*?)```", resp, re.S)
            code = m.group(1) if m else ""
            bad = unsafe_python(code) if code else "no python block"
        if not code:
            result["reason"] = "no python block"
        else:
            (sdir / "script.py").write_text(code)
            if bad:
                result["reason"] = f"unsafe construct rejected: {bad}"
            else:
                t0 = time.time()
                try:
                    r = subprocess.run([sys.executable, "-I", str(sdir / "script.py")], capture_output=True, text=True,
                                       timeout=cap_s + 30, cwd=str(sdir), env={"PATH": "/usr/bin:/bin", "HOME": str(sdir)})
                    out = r.stdout
                    (sdir / "stdout.txt").write_text(out[-20000:] + ("\n[stderr]\n" + r.stderr[-4000:] if r.stderr else ""))
                    hit = None
                    for line in reversed(out.splitlines()):
                        if line.startswith("WITNESS:"):
                            try:
                                hit = json.loads(line[len("WITNESS:"):].strip())
                            except json.JSONDecodeError:
                                hit = {"raw": line[len("WITNESS:"):].strip()}
                            break
                    result = {"status": "found" if hit is not None else "none", "kind": kind, "witness": hit,
                              "elapsed_s": round(time.time() - t0, 1), "rc": r.returncode}
                except subprocess.TimeoutExpired:
                    result = {"status": "none", "kind": kind, "reason": "timeout", "elapsed_s": cap_s + 30}
        self.state["search"] = result
        self.save()
        if result.get("status") == "found":
            (sdir / "witness.json").write_text(json.dumps(result["witness"], indent=2))
        self.log.event("search", result["status"], kind=kind, witness=json.dumps(result.get("witness"))[:300],
                       reason=result.get("reason"), elapsed=result.get("elapsed_s"))

    # -- open mode: both directions ---------------------------------------------------------------

    def _negate_statement(self, pos: str) -> str | None:
        """Build `theorem erdos_N_neg : ¬ (<type of erdos_N>)` from the frozen positive statement, using Lean's own
        `#check` output for the type; keeps any `def`s that precede the theorem. Returns None if it does not compile."""
        thm = f"erdos_{self.problem['id']}"
        res = self.check(pos + f"\n\n#check @{thm}\n", "negation-check")
        typ = None
        for msg in res["infos"]:
            mm = re.search(rf"{re.escape(thm)}\s*:\s*(.*)", msg, re.S)
            if mm:
                typ = " ".join(mm.group(1).split())
                break
        if not typ:
            return None
        idx = pos.find("theorem ")
        prelude = pos[:idx] if idx > 0 else ""
        neg = f"{prelude}theorem {thm}_neg : ¬ ({typ}) := by\n  sorry"
        chk = self.check(neg, "negation-compile")
        return neg if chk["ok"] else None

    def run_open(self) -> int:
        """Formalize the conjecture AND its negation, freeze both, attack both in parallel, report which (if any)
        was proved. Everything lands in knowledge/open/<n>/<run>/ marked for human review."""
        pid = self.problem["id"]
        self.log.event("open", "start", problem=pid)
        self.stage_formalize()
        pos = self.state["statement"]
        self.stage_assess()
        neg = self.state.get("statement_neg") or self._negate_statement(pos)
        if not neg:
            resp = self.ask("formalize", NEGATION_PROMPT.format(statement=pos, pid=pid))
            blocks = [b for b in lean_blocks(resp) if f"erdos_{pid}_neg" in b]
            for b in blocks:
                if self.check(b, "negation-llm")["ok"] and "¬" in b:
                    neg = b
                    break
        if not neg:
            self.log.event("open", "negation_failed")
            self.report(False)
            return 2
        self.state["statement_neg"] = neg
        self.save()
        self.log.event("open", "frozen_both", pos=pos[:200], neg=neg[:200])
        children, results = {}, {}
        budget = getattr(self.args, "run_budget", None)
        for direction, stmt in (("pos", pos), ("neg", neg)):
            cdir = self.run_dir / direction
            cdir.mkdir(exist_ok=True)
            if not (cdir / "state.json").exists():
                st = {k: self.state[k] for k in ("literature", "crosscheck", "formalize_notes", "verified_names",
                                                 "assessment", "mode", "mode_reason") if k in self.state}
                st.update({"statement": stmt, "problem_input": self.problem, "direction": direction, "invocations": []})
                (cdir / "state.json").write_text(json.dumps(st, indent=2))
            cargs = argparse.Namespace(**vars(self.args))
            cargs.resume, cargs.open = str(cdir), False
            cargs.run_budget = (budget / 2) if budget else None
            h = Harness(cargs)
            h.thm_name = f"erdos_{pid}" if direction == "pos" else f"erdos_{pid}_neg"
            h.direction = direction
            children[direction] = h

        def go(direction):
            try:
                results[direction] = children[direction].run()
            except BaseException as e:   # noqa: BLE001 — recorded, the other direction continues
                results[direction] = f"error: {repr(e)[:200]}"

        threads = [threading.Thread(target=go, args=(d,), daemon=True) for d in children]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        out = KNOWLEDGE / "open" / pid / self.run_dir.name
        out.mkdir(parents=True, exist_ok=True)
        lines = [f"# Open problem #{pid} — two-direction attack (run {self.run_dir.name})", "",
                 "**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be "
                 "subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.", "",
                 f"- English statement: {self.problem['statement']}", f"- triage: {self.state.get('mode')} — {self.state.get('mode_reason')}", ""]
        proved_any = partial_any = False
        for direction in ("pos", "neg"):
            h = children[direction]
            v = h.state.get("verify", {})
            outcome = h.state.get("outcome", "?")
            rc = results.get(direction)
            proved_any |= (rc == 0)
            partial_any |= (rc == 3)
            lines += [f"Review milestones: {json.dumps(h.state.get('solution_review', {}))}"]
            lines += [f"## Direction `{direction}` — outcome: **{outcome}** (exit {rc})", "```lean", h.state.get("statement", ""), "```"]
            if rc == 0 and h.state.get("proof"):
                (out / f"Erdos{pid}_{direction}.lean").write_text(compose(h.state["proof"], h.imports))
                lines += [f"- verified proof saved: `{out / f'Erdos{pid}_{direction}.lean'}`",
                          f"- faithfulness judge: {json.dumps(v.get('faithful'))[:600]}", f"- axioms: {v.get('axioms')}"]
            if h.state.get("partial"):
                lines += [f"- partial results: {h.state['partial']}"]
            s = h.state.get("search") or {}
            if s.get("status") == "found":
                lines += [f"- search {s.get('kind')}: {json.dumps(s.get('witness'))[:300]}"]
            lines += [f"- spent: ${h.spent_usd():.2f}", ""]
        (out / "report.md").write_text("\n".join(lines) + "\n")
        (self.run_dir / "report.md").write_text("\n".join(lines) + "\n")
        self.state["open_reviews"] = {d: h.state.get("solution_review", {}) for d, h in children.items()}
        self.state["open_results"] = {d: results.get(d) for d in children}
        self.save()
        rc = 0 if proved_any else 3 if partial_any else 2
        self.log.event("open", "end", results=self.state["open_results"], exit=rc, dir=str(out))
        (self.run_dir / "DONE").write_text(json.dumps({"open": self.state["open_results"], "exit": rc, "open_reviews": self.state["open_reviews"]}))
        return rc

    # -- construction search (gated by --allow-construct) ------------------------------------------

    def _run_py(self, script: Path, timeout: int, cwd: Path) -> tuple[int, str]:
        try:
            r = subprocess.run([sys.executable, "-I", str(script)], capture_output=True, text=True, timeout=timeout,
                               cwd=str(cwd), env={"PATH": "/usr/bin:/bin", "HOME": str(cwd)})
            return r.returncode, (r.stdout[-30000:] + ("\n[stderr]\n" + r.stderr[-3000:] if r.stderr else ""))
        except subprocess.TimeoutExpired:
            return -9, "[timeout]"

    def stage_construct(self):
        """FunSearch-lite for extremal/bound targets: the model writes a generator + scorer + Lean-certificate program
        for finite candidate objects; a loop alternates random local search over the program's parameters/mutations
        with model-proposed program variants, keeps an archive, and finally compiles a Lean certificate of the best
        object's finite property. Output: knowledge/constructions/<n>/<run>/ labelled 'certified bound, not a resolution'."""
        if "construct" in self.state:
            return
        cdir = self.run_dir / "construct"
        cdir.mkdir(exist_ok=True)
        budget = float(getattr(self.args, "construct_budget", 10.0))
        wall_cap = int(getattr(self.args, "construct_wall", 1800))
        iters = int(getattr(self.args, "construct_iters", 4))
        per_iter_s = int(getattr(self.args, "construct_seconds", 120))
        t_start, spent0 = time.time(), self.spent_usd()
        known = self.state.get("known_bound") or (self.state.get("assessment") or {}).get("known_bound")
        archive: list[dict] = []
        program = ""
        result = {"status": "none", "iterations": 0, "archive": [], "known_bound": known}
        (cdir / "driver.py").write_text(CONSTRUCT_DRIVER)
        for it in range(1, iters + 1):
            if time.time() - t_start > wall_cap or self.spent_usd() - spent0 > budget:
                result["stopped"] = "wall-clock cap" if time.time() - t_start > wall_cap else "construct budget"
                break
            summary = json.dumps([{"score": a["score"], "describe": a.get("describe", "")[:200]} for a in archive[:5]])
            resp = self.ask("construct", CONSTRUCT_PROMPT.format(
                pid=self.problem["id"], statement_en=self.problem["statement"], notes=(self.problem.get("notes") or "")[:2500],
                statement=self.state["statement"], known=known or "unknown", iteration=it, archive=summary or "[]",
                program=program[:12000] if program else "(none yet — write the first version)"))
            m = re.search(r"```python\s*\n(.*?)```", resp, re.S)
            if not m:
                self.log.event("construct", "no_program", iteration=it)
                continue
            code = m.group(1)
            bad = unsafe_python(code)
            if bad:
                self.log.event("construct", "unsafe_program", iteration=it, construct=bad)
                continue
            program = code
            (cdir / f"program-{it}.py").write_text(code)
            (cdir / "program.py").write_text(code)
            (cdir / "config.json").write_text(json.dumps({"seconds": per_iter_s, "seed": it, "archive_in": archive[:5]}))
            rc, out = self._run_py(cdir / "driver.py", per_iter_s + 60, cdir)
            (cdir / f"driver-out-{it}.txt").write_text(out)
            found = None
            for line in reversed(out.splitlines()):
                if line.startswith("ARCHIVE:"):
                    try:
                        found = json.loads(line[len("ARCHIVE:"):])
                    except json.JSONDecodeError:
                        found = None
                    break
            if not found:
                self.log.event("construct", "driver_failed", iteration=it, rc=rc, tail=out[-300:])
                continue
            for a in found:
                a["iteration"] = it
            archive = sorted(archive + found, key=lambda a: -a["score"])[:10]
            self.log.event("construct", "iteration", iteration=it, best=archive[0]["score"] if archive else None,
                           n_new=len(found), secs=round(time.time() - t_start))
            result["iterations"] = it
        if not archive:
            result["status"] = "no_objects"
            self.state["construct"] = result
            self.save()
            self.log.event("construct", "done", **{k: v for k, v in result.items() if k != "archive"})
            return
        best = archive[0]
        cert = best.get("certificate") or ""
        certified = False
        if cert.strip():
            # certificates get a longer Lean timeout than proof attempts (kernel evaluation of Bool checks)
            slow = LeanChecker(FORMAL, max(self.args.lean_timeout, 900))
            res = slow.check(compose(cert, self.imports), self.run_dir / "attempts" / "construct-certificate.lean")
            certified = res["ok"] and not res["sorries"] and not has_banned(cert)
            self.log.event("lean", "check", name="construct-certificate", ok=res["ok"], sorries=res["sorries"],
                           n_errors=len(res["errors"]), first_error=(res["errors"][0] if res["errors"] else ""))
            result["certificate_errors"] = res["errors"][:3]
            if not certified and len(archive) > 1:
                # fall back to the next-best object whose certificate compiles (smaller objects certify faster)
                for alt in archive[1:4]:
                    c2 = alt.get("certificate") or ""
                    if not c2.strip() or has_banned(c2):
                        continue
                    r2 = slow.check(compose(c2, self.imports), self.run_dir / "attempts" / "construct-certificate-alt.lean")
                    if r2["ok"] and not r2["sorries"]:
                        best, cert, certified = alt, c2, True
                        result["certified_fallback"] = True
                        break
        result.update({"status": "certified" if certified else "uncertified", "best": {k: v for k, v in best.items() if k != "certificate"},
                       "archive": [{k: v for k, v in a.items() if k != "certificate"} for a in archive[:5]]})
        out = KNOWLEDGE / "constructions" / self.problem["id"] / self.run_dir.name
        out.mkdir(parents=True, exist_ok=True)
        (out / "object.json").write_text(json.dumps(best.get("object"), indent=2))
        (out / "program.py").write_text(program)
        if cert.strip():
            (out / "certificate.lean").write_text(compose(cert, self.imports))
        cmp_line = f"known bound (literature/triage): {known or 'unknown'}; achieved score: {best['score']}"
        (out / "report.md").write_text(
            f"# Construction — Erdős #{self.problem['id']} (run {self.run_dir.name})\n\n"
            f"**CERTIFIED BOUND, NOT A RESOLUTION.** Lean certificate {'compiled' if certified else 'did NOT compile'} for the finite "
            f"property of the best object found. Requires human review before any external claim.\n\n- {cmp_line}\n"
            f"- object: `{json.dumps(best.get('object'))[:500]}`\n- description: {best.get('describe', '')[:400]}\n"
            f"- iterations: {result['iterations']}; archive top scores: {[a['score'] for a in archive[:5]]}\n\n"
            "## Frozen target (unproved)\n```lean\n" + self.state["statement"] + "\n```\n")
        result["dir"] = str(out)
        self.state["construct"] = result
        self.save()
        self.log.event("construct", "done", status=result["status"], best=best["score"], dir=str(out))

    # -- research program (gated by --allow-research) ----------------------------------------------

    def _program_dir(self) -> Path:
        d = ROOT / "programs" / f"erdos_{self.problem['id']}"
        d.mkdir(parents=True, exist_ok=True)
        return d

    def _install_lemmas_module(self, pdir: Path) -> str | None:
        """Compile programs/erdos_<n>/Lemmas.lean as module Formal.Programs.Erdos<n> so later attempts can import it."""
        src = pdir / "Lemmas.lean"
        if not src.exists() or not src.read_text().strip():
            return None
        mod_dir = FORMAL / "Formal" / "Programs"
        mod_dir.mkdir(parents=True, exist_ok=True)
        mod_name = f"Formal.Programs.Erdos{self.problem['id']}"
        # a real Lean module: import header (problem imports + every `-- IMPORTS:` directive in the lemmas) + options
        (mod_dir / f"Erdos{self.problem['id']}.lean").write_text(compose(src.read_text(), self.imports))
        try:
            r = subprocess.run(["lake", "build", mod_name], cwd=FORMAL, capture_output=True, text=True, timeout=900, env=clean_env())
            ok = r.returncode == 0
        except subprocess.TimeoutExpired:
            ok = False
        self.log.event("program", "lemmas_module", module=mod_name, ok=ok)
        return mod_name if ok else None

    def run_program(self) -> int:
        """Persistent research program: PLAN.md ↔ numerical experiments ↔ sub-statements attacked with the standard
        pipeline ↔ certified lemmas accumulated in Lemmas.lean (a real Lean module) ↔ retrospect; REVIEW.md every k
        cycles with a pause for human direction via the file backend. Exit 3 = partial progress."""
        pid = self.problem["id"]
        if not getattr(self.args, "run_budget", None):
            self.log.event("program", "refused", detail="--allow-research requires --run-budget")
            self.report(False)
            return 2
        pdir = self._program_dir()
        plan_path, lemmas_path, ledger = pdir / "PLAN.md", pdir / "Lemmas.lean", pdir / "ledger.jsonl"
        lemmas_path.touch()
        cycles = int(getattr(self.args, "research_cycles", 2))
        review_every = int(getattr(self.args, "review_every", 2))
        certified_any = False
        for cycle in range(1, cycles + 1):
            try:
                cdir = pdir / "cycles" / f"{datetime.now().strftime('%Y%m%d-%H%M%S')}-c{cycle}"
                cdir.mkdir(parents=True, exist_ok=True)
                plan = plan_path.read_text() if plan_path.exists() else ""
                lemmas = lemmas_path.read_text()
                ledger_txt = ledger.read_text() if ledger.exists() else ""
                # (a) numerical experiments
                resp = self.ask("experiments", EXPERIMENTS_PROMPT.format(
                    pid=pid, statement_en=self.problem["statement"], statement=self.state["statement"],
                    literature=(self.state.get("literature") or "")[:4000], plan=plan[-6000:] or "(no plan yet)"))
                exp_out = ""
                m = re.search(r"```python\s*\n(.*?)```", resp, re.S)
                if m and unsafe_python(m.group(1)):
                    bad = unsafe_python(m.group(1))
                    resp = self.ask("experiments", EXPERIMENTS_PROMPT.format(
                        pid=pid, statement_en=self.problem["statement"], statement=self.state["statement"],
                        literature=(self.state.get("literature") or "")[:4000], plan=plan[-6000:] or "(no plan yet)")
                        + f"\n\nYour previous script was REJECTED by the safety screen for `{bad}`; allowed modules: "
                          f"{', '.join(sorted(ALLOWED_PY_MODULES))}.")
                    m = re.search(r"```python\s*\n(.*?)```", resp, re.S)
                if not m:
                    self.log.event("program", "experiments_skipped", cycle=cycle, reason="no python block in response")
                elif unsafe_python(m.group(1)):
                    self.log.event("program", "experiments_skipped", cycle=cycle, reason=f"unsafe: {unsafe_python(m.group(1))}")
                else:
                    (cdir / "experiments.py").write_text(m.group(1))
                    rc, exp_out = self._run_py(cdir / "experiments.py", 180, cdir)
                    (cdir / "experiments.txt").write_text(exp_out)
                    self.log.event("program", "experiments_ran", cycle=cycle, rc=rc, lines=len(exp_out.splitlines()))
                # (b) plan + sub-statements
                resp = self.ask("plan", PLAN_PROMPT.format(
                    pid=pid, statement_en=self.problem["statement"], statement=self.state["statement"],
                    literature=(self.state.get("literature") or "")[:4000], plan=plan[-6000:] or "(none yet)",
                    experiments=exp_out[-4000:] or "(none)", lemmas=lemmas[-6000:] or "(empty)", ledger=ledger_txt[-3000:] or "(empty)",
                    cycle=cycle))
                pm = re.search(r"```markdown\s*\n(.*?)```", resp, re.S)
                if pm:
                    plan_path.write_text(pm.group(1))
                subs = [b for b in lean_blocks(resp) if re.search(rf"theorem\s+erdos_{pid}_sub\w*", b)]
                self.log.event("program", "cycle_plan", cycle=cycle, substatements=len(subs))
                # (c) attack each sub-statement with the standard pipeline (child run, Lemmas module imported)
                module = self._install_lemmas_module(pdir)
                new_lemmas = 0
                for i, sub in enumerate(subs[:5]):
                    chk = self.check(sub, f"sub-c{cycle}-{i}")
                    if not (chk["ok"] and chk["sorries"]):
                        self.log.event("program", "substatement_rejected", cycle=cycle, i=i, error=(chk["errors"][:1] or [""])[0][:200])
                        continue
                    name = re.search(rf"theorem\s+(erdos_{pid}_sub\w*)", sub).group(1)
                    sdir = cdir / f"sub-{i}"
                    sdir.mkdir(exist_ok=True)
                    st = {"literature": self.state.get("literature", ""), "statement": sub, "problem_input": self.problem,
                          "crosscheck": {"ranking": [0], "issues": {"0": "program sub-statement (not the frozen target)"}},
                          "mode": "fast", "mode_reason": "research-program sub-goal", "invocations": []}
                    (sdir / "state.json").write_text(json.dumps(st, indent=2))
                    cargs = argparse.Namespace(**vars(self.args))
                    cargs.resume, cargs.open, cargs.allow_research, cargs.skip_assess = str(sdir), False, False, True
                    cargs.run_budget = max(3.0, (self.args.run_budget - self.spent_usd()) / max(1, len(subs) - i))
                    child = Harness(cargs)
                    child.thm_name = name
                    child.direction = "program"
                    if module:
                        child.imports = list(dict.fromkeys(child.imports + [module]))
                    try:
                        rc = child.run()
                    except Harness.BudgetExhausted:
                        rc = 2
                    entry = {"cycle": cycle, "sub": name, "run": str(sdir), "exit": rc, "verified": rc == 0,
                             "statement": sub.splitlines()[0][:200], "at": now()}
                    with open(ledger, "a") as f:
                        f.write(json.dumps(entry) + "\n")
                    if rc == 0 and child.state.get("proof"):
                        # (d) move the certified result into the library: keep `-- IMPORTS:` directives (compose() turns them
                        # into header imports) and isolate each block in its own namespace so private helpers cannot clash
                        body = strip_imports(child.state["proof"])
                        with open(lemmas_path, "a") as f:
                            f.write(f"\n-- certified in {sdir.name} ({now()})\nnamespace {name}_ns\n{body}\nend {name}_ns\n")
                        new_lemmas += 1
                        certified_any = True
                        self.log.event("program", "lemma_certified", cycle=cycle, name=name)
                    self._check_run_budget("program")
                if new_lemmas:
                    self._install_lemmas_module(pdir)
                # (e) retrospect on the cycle's runs (cheap; lessons go to the playbook)
                for sdir in sorted(cdir.glob("sub-*")):
                    if (sdir / "state.json").exists() and json.loads((sdir / "state.json").read_text()).get("proof"):
                        try:
                            subprocess.run([sys.executable, str(ROOT / "harness.py"), "retrospect", str(sdir)], cwd=ROOT,
                                           capture_output=True, text=True, timeout=900)
                        except Exception:   # noqa: BLE001
                            pass
                # (f) review + pause
                if cycle % review_every == 0 or cycle == cycles:
                    review = (f"# REVIEW — Erdős #{pid}, after cycle {cycle} ({now()})\n\n**Requires human direction.** Nothing here is a "
                              f"resolution; certified lemmas are in Lemmas.lean.\n\n## Plan\n{plan_path.read_text() if plan_path.exists() else ''}\n\n"
                              f"## Ledger\n```\n{ledger.read_text() if ledger.exists() else ''}\n```\n\n## Experiments (last)\n```\n{exp_out[-3000:]}\n```\n"
                              f"\nSpent so far: ${self.spent_usd():.2f} of ${self.args.run_budget}.\n")
                    (pdir / "REVIEW.md").write_text(review)
                    wait_s = int(getattr(self.args, "review_wait", 0))
                    self.log.event("program", "review_written", cycle=cycle, path=str(pdir / "REVIEW.md"), wait_s=wait_s)
                    if wait_s > 0 and cycle < cycles:
                        fb = FileBackend(self.run_dir, wait_s)
                        try:
                            direction = fb.complete("review", review + "\n\nWrite your direction for the next cycles as plain text.")
                            with open(plan_path, "a") as f:
                                f.write(f"\n\n## HUMAN DIRECTION ({now()})\n{direction}\n")
                        except TimeoutError:
                            self.log.event("program", "paused_no_direction", cycle=cycle)
                            break
            except Harness.BudgetExhausted as e:
                self.log.event("program", "stopped_on_budget", cycle=cycle, detail=str(e))
                break
        self.state["program"] = {"dir": str(pdir), "certified_any": certified_any,
                                 "ledger_entries": sum(1 for _ in open(ledger)) if ledger.exists() else 0}
        self.state["outcome"] = "partial" if certified_any else "not_proved"
        self.state["stop_reason"] = "research program cycles finished (see programs/erdos_%s/REVIEW.md)" % pid
        self.save()
        self.report(False)
        return 3 if certified_any else 2

    # -- partial results (exit code 3): sorry-free lemmas / special cases salvaged from failed searches

    @staticmethod
    def _split_decls(code: str) -> list[str]:
        return [b for b in re.split(r"\n(?=(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*"
                                    r"(?:lemma|theorem|def|abbrev|instance|structure|inductive)\s)", code) if b.strip()]

    def stage_partial(self) -> bool:
        """Salvage sorry-free helper lemmas (special cases, bounds) from the best failed material, compile them
        WITHOUT the main theorem, and store them in knowledge/partial/<n>/<run>/ as an attributed partial result."""
        sources = []
        dec = self.state.get("decomposition") or {}
        if isinstance(dec, dict) and dec.get("code"):
            sources.append(dec["code"])
        sources += [a["code"] for a in self._best_partials(self.state.get("attempts", []), 4) if a.get("code")]
        if not sources:
            return False
        main = f"erdos_{self.problem['id']}"
        kept, seen = [], set()
        for src in sources:
            for d in self._split_decls(src):
                if re.match(r"^--\s*IMPORTS?:", d.strip()):
                    kept.append(d) if d not in seen else None
                    seen.add(d)
                    continue
                m = re.match(r"(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(lemma|theorem|def|abbrev|instance|structure|inductive)\s+(\S+)", d.strip())
                if not m or m.group(2) == main or hole_count(d) or has_banned(d):
                    continue
                key = norm_ws(strip_comment_lines(d))
                if key in seen:
                    continue
                seen.add(key)
                kept.append(d)
        lemmas = [d for d in kept if re.search(r"\b(?:lemma|theorem)\b", d.split(":=")[0])]
        if not lemmas:
            return False
        body = "\n\n".join(kept)
        res = self.check(body, "partial")
        if not res["ok"] or res["sorries"]:
            # try each lemma alone with the defs, keep the ones that compile
            defs = [d for d in kept if d not in lemmas]
            good = []
            for lem in lemmas:
                r = self.check("\n\n".join(defs + [lem]), f"partial-{len(good)}")
                if r["ok"] and not r["sorries"]:
                    good.append(lem)
            if not good:
                return False
            lemmas, body = good, "\n\n".join(defs + good)
        run_label = self.run_dir.name if not getattr(self, "direction", None) else f"{self.run_dir.parent.name}-{self.run_dir.name}"
        out = KNOWLEDGE / "partial" / self.problem["id"] / run_label
        out.mkdir(parents=True, exist_ok=True)
        (out / "partial.lean").write_text(compose(body, self.imports))
        names = [re.match(r"(?:private\s+|protected\s+)?(?:lemma|theorem)\s+(\S+)", l.strip()).group(1) for l in lemmas]
        (out / "report.md").write_text(
            f"# Partial result — Erdős #{self.problem['id']} (run {self.run_dir.name})\n\n"
            "**Status: PARTIAL — the main theorem was NOT proved.** These sorry-free auxiliary lemmas compiled against "
            "the frozen setting and are kept for reuse. They are NOT a resolution of the problem and require human "
            "review before any external claim.\n\n## Frozen target (unproved)\n```lean\n" + self.state.get("statement", "") +
            "\n```\n\n## Compiled lemmas\n" + "\n".join(f"- `{n}`" for n in names) +
            "\n\n```lean\n" + body + "\n```\n")
        self.state["partial"] = {"dir": str(out), "lemmas": names}
        self.save()
        self.log.event("partial", "saved", lemmas=names, dir=str(out))
        return True


# --------------------------------------------------------------------------- self-improvement commands

RETROSPECT_PROMPT = """You are the retrospective stage of a Lean 4 proof harness. Below is the digest of one run:
the problem, the frozen statement, what the compiler rejected (with the code and its exact errors), and the
proof that finally compiled (if any). Extract at most 3 GENERAL, REUSABLE lessons about writing Lean 4 /
Mathlib proofs that would have saved rounds here and would plausibly help on OTHER problems (tactic
idioms, lemma names that exist vs. do not, import/notation pitfalls, encoding choices). Do NOT restate the
problem-specific mathematics. Each lesson: 1-2 sentences, ≤ 300 characters, concrete (name the tactics /
lemmas), and true for current Mathlib. Skip lessons already present in the EXISTING PLAYBOOK.

EXISTING PLAYBOOK:
{playbook}

RUN DIGEST:
{digest}

Respond with EXACTLY one ```json block: {{"entries": [{{"tags": ["k1", "k2"], "text": "..."}}, ...]}}
(tags: 2-5 lowercase keywords such a problem would mention: factorial, finset, colouring, cast, infinite...)."""


def run_digest(run_dir: Path, max_attempts: int = 6) -> str:
    st = json.loads((run_dir / "state.json").read_text())
    pid = re.search(r"erdos(\d+)", run_dir.name)
    pid = pid.group(1) if pid else "?"
    parts = [f"PROBLEM #{pid}", f"FROZEN STATEMENT:\n{st.get('statement', '')}"]
    attempts = st.get("attempts", [])
    shown = 0
    for a in attempts:
        if shown >= max_attempts:
            break
        if a.get("rejected"):
            parts.append(f"REJECTED before compile ({a['name']}): {a['errors'][0]}")
            continue
        code = a.get("code", "")
        if code:
            parts.append(f"FAILED ATTEMPT {a['name']} [{a.get('plan', '')[:100]}]:\n```lean\n{code[:3000]}\n```\nERRORS:\n"
                         + "\n".join("  " + e[:500] for e in a.get("errors", [])[:5]))
            shown += 1
    if st.get("proof"):
        parts.append(f"PROOF THAT COMPILED:\n```lean\n{st['proof'][:6000]}\n```")
    else:
        parts.append("NO PROOF WAS FOUND.")
    return "\n\n".join(parts)


def append_playbook(entries: list[dict], provenance: str) -> int:
    import difflib
    KNOWLEDGE.mkdir(exist_ok=True)
    path = KNOWLEDGE / "playbook.md"
    existing = playbook_entries()
    added = 0
    with open(path, "a") as f:
        for e in entries:
            text = " ".join(str(e.get("text", "")).split())
            tags = [str(t).strip().lower() for t in e.get("tags", []) if str(t).strip()][:6]
            if not text or len(text) > 400:
                continue
            if any(difflib.SequenceMatcher(None, text.lower(), x["text"].lower()).ratio() > 0.75 for x in existing):
                continue
            f.write(f"\n- [tags: {', '.join(tags)}] {text}  <!-- {provenance} -->\n")
            existing.append({"tags": tags, "text": text})
            added += 1
    return added


def cmd_retrospect(args) -> int:
    run_dir = Path(args.run_dir).resolve()
    digest = run_digest(run_dir)
    llm = CodexCliBackend(args.model, 900) if getattr(args, "backend", "claude-cli") == "codex-cli" else ClaudeCliBackend(args.model, 900, 3.0)
    pb = "\n".join("- " + e["text"] for e in playbook_entries()) or "(empty)"
    resp = llm.complete("retrospect", RETROSPECT_PROMPT.format(playbook=pb[:6000], digest=digest[:30000]))
    (run_dir / "retrospect.md").write_text(f"# retrospect\n\n## digest\n\n{digest}\n\n## response\n\n{resp}\n")
    data = json_block(resp)
    entries = (data or {}).get("entries", []) if isinstance(data, dict) else []
    n = append_playbook(entries, f"from {run_dir.name}")
    st = json.loads((run_dir / "state.json").read_text())
    m = harvest_lemmas(st["proof"], run_dir.name.split("erdos")[-1], run_dir.name) if st.get("proof") and st.get("verify", {}).get("all_clear") else 0
    print(f"retrospect: {len(entries)} proposed, {n} playbook entries added, {m} lemmas harvested (cost {getattr(llm, 'total_cost_usd', 'unavailable')})")
    return 0


def cmd_regress(args) -> int:
    """Fast: every verified proof in knowledge/solved/ must still compile sorry-free with clean axioms under the
    CURRENT harness (imports, compose, banned-construct rules). Full: re-run the pipeline for the given problems."""
    checker = LeanChecker(FORMAL, args.lean_timeout)
    rows = []
    solved = sorted((KNOWLEDGE / "solved").glob("Erdos*.lean")) if (KNOWLEDGE / "solved").exists() else []
    if getattr(args, "references", False):
        solved += sorted((ROOT / "references").glob("Erdos*.lean"))
    if getattr(args, 'only', None):
        solved = [p for p in solved if p.stem.removeprefix('Erdos') in args.only]
    if not solved:
        print("regress: no verified proofs in knowledge/solved/ yet")
    out_dir = RUNS / "regress"
    out_dir.mkdir(parents=True, exist_ok=True)
    replay_id = datetime.now().strftime('%Y%m%d-%H%M%S-%f')
    def one(path: Path):
        test_dir = out_dir / replay_id / path.parent.name / path.stem
        test_dir.mkdir(parents=True, exist_ok=True)
        pid = path.stem.removeprefix('Erdos')
        test_state = {'problem_input': {'id': pid}, 'outcome': 'running', 'test_kind': 'saved_proof_replay'}
        feed_atomic(test_dir / 'state.json', test_state)
        test_log = RunLog(test_dir)
        test_log.event('regression', 'start')
        src = path.read_text()
        thm = re.search(r"theorem\s+(erdos_\d+)", src)
        thm = thm.group(1) if thm else "erdos_?"
        banned = has_banned(strip_imports(src))
        try:
            res = checker.check(src + f"\n#print axioms {thm}\n", out_dir / path.name)
        except BaseException:
            test_state['outcome'] = 'infrastructure_error'
            feed_atomic(test_dir / 'state.json', test_state)
            test_log.event('regression', 'fatal')
            feed_atomic(test_dir / 'DONE', {'fatal': 'replay infrastructure error'})
            export_run(test_dir)
            raise
        m = re.search(rf"'{re.escape(thm)}' depends on axioms:\s*\[([^\]]*)\]", res["raw"])
        axioms = {t.strip() for t in m.group(1).split(",") if t.strip()} if m else set()
        ok = res["ok"] and not res["sorries"] and not banned and (axioms <= STD_AXIOMS) and (m is not None or "does not depend on any axioms" in res["raw"])
        test_state['outcome'] = 'regression_passed' if ok else 'regression_failed'
        test_state['test_result'] = {'passed': bool(ok), 'compiles': res['ok'], 'axioms': sorted(axioms)}
        feed_atomic(test_dir / 'state.json', test_state)
        test_log.event('regression', 'passed' if ok else 'failed')
        feed_atomic(test_dir / 'DONE', {'passed': bool(ok)})
        export_run(test_dir)
        return (path.stem, ok, res["ok"], res["sorries"], banned, sorted(axioms), (res["errors"][:1] or [""])[0][:200])
    with ThreadPoolExecutor(max_workers=COMPILE_WORKERS) as ex:
        rows = list(ex.map(one, solved))
    lines = ["| proof | PASS | compiles | sorry | banned | axioms | first error |", "|---|---|---|---|---|---|---|"]
    for r in rows:
        lines.append(f"| {r[0]} | {'✅' if r[1] else '❌'} | {r[2]} | {r[3]} | {r[4]} | {','.join(r[5])} | {r[6]} |")
    table = "\n".join(lines)
    print(table)
    full_rows = []
    if args.full:
        for pid in args.problems:
            prob = ROOT / "problems" / f"erdos_{pid}.json"
            cmd = [sys.executable, str(ROOT / "harness.py"), "run", "--problem", str(prob), "--backend", "claude-cli",
                   "--rounds", str(args.rounds), "--decompose-rounds", str(args.decompose_rounds)] + \
                  (["--agentic", args.agentic] if args.agentic else [])
            t0 = time.time()
            r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
            m = re.search(r"run/end .*'proved': (True|False).*'all_clear': (True|False|None)", r.stdout)
            full_rows.append((pid, r.returncode == 0, m.group(2) if m else "?", round((time.time() - t0) / 60, 1)))
            print(f"full regress #{pid}: proved={r.returncode == 0} all_clear={m.group(2) if m else '?'} ({full_rows[-1][3]} min)")
    report = f"# regress {now()}\n\n## fast (recompile verified proofs)\n\n{table}\n"
    if full_rows:
        report += "\n## full (pipeline re-runs)\n\n| problem | proved | all_clear | minutes |\n|---|---|---|---|\n" + \
                  "\n".join(f"| {p} | {a} | {b} | {c} |" for p, a, b, c in full_rows) + "\n"
    (out_dir / f"regress-{datetime.now().strftime('%Y%m%d-%H%M%S')}.md").write_text(report)
    failed = [r for r in rows if not r[1]] + [r for r in full_rows if not r[1]]
    print(f"regress: {len(rows) + len(full_rows) - len(failed)} passed, {len(failed)} failed")
    return 1 if failed else 0


def promotion_decision(before, after):
    """Require a strict held-out gain and preservation of every previous success."""
    if not before or before.keys() != after.keys():
        return False
    if any(type(v) is not bool for v in [*before.values(), *after.values()]):
        return False
    return all(not before[k] or after[k] for k in before) and sum(after.values()) > sum(before.values())


def cmd_improve(args) -> int:
    # Kept in a separate module to make the evaluation/promotion workflow reviewable.
    from learning import improve
    return improve(args)


# --------------------------------------------------------------------------- scout: open-problem triage from the database

SITE_UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
           "Chrome/128.0 Safari/537.36")
SITE_CACHE = RUNS / ".cache" / "site"


def ensure_erdos_db() -> Path:
    """teorth/erdosproblems data/problems.yaml, cloned (depth 1) into runs/.cache if absent."""
    d = RUNS / ".cache" / "erdosproblems"
    f = d / "data" / "problems.yaml"
    if not f.exists():
        d.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", "-q", "--depth", "1", "https://github.com/teorth/erdosproblems.git", str(d)],
                       check=True, timeout=300, env=clean_env())
    return f


def fetch_problem_page(n: str | int, refresh: bool = False, pause: float = 0.4) -> str:
    """erdosproblems.com/<n> HTML (browser UA; the site 403s generic fetchers), cached on disk."""
    SITE_CACHE.mkdir(parents=True, exist_ok=True)
    cache = SITE_CACHE / f"{n}.html"
    if cache.exists() and not refresh:
        return cache.read_text(errors="replace")
    req = urllib.request.Request(f"https://www.erdosproblems.com/{n}", headers={"User-Agent": SITE_UA, "Accept": "text/html"})
    with urllib.request.urlopen(req, timeout=30) as r:
        html_text = r.read().decode(errors="replace")
    cache.write_text(html_text)
    time.sleep(pause)
    return html_text


def parse_problem_page(html_text: str) -> dict:
    """Extract the status line, statement, site discussion, comment count and ambiguity flags from a problem page."""
    import html as _html
    h = re.sub(r"<script.*?</script>|<style.*?</style>", "", html_text, flags=re.S)
    h = re.sub(r"<br\s*/?>|</p>|</div>|</li>|</h\d>", "\n", h)
    t = _html.unescape(re.sub(r"<[^>]+>", "", h))
    t = re.sub(r"[ \t]+", " ", t)
    t = re.sub(r"\n\s*\n+", "\n", t)
    body = t.split("Random Open\n", 1)[1] if "Random Open\n" in t else t
    body = re.split(r"\n\s*(?:Additional thanks to|Proof expositions \()", body)[0].strip()
    lines = [l.strip() for l in body.splitlines() if l.strip()]
    status_line = lines[0] if lines else ""
    # statement = lines after the status sentence(s) up to the "#N: [refs]" line; discussion = after the tag lines
    stmt, disc, seen_ref, tags = [], [], False, []
    status_sentences = ("This has been", "Open, but could be", "This is open, and cannot", "Resolved up to a finite",
                        "This problem is open", "This is ")
    for l in lines[1:]:
        if not seen_ref:
            if re.match(r"^#\d+:", l):
                seen_ref = True
                continue
            if not stmt and l.startswith(status_sentences) and ("Lean" in l or "finite" in l or "open" in l.lower() or l.startswith("This has been")):
                continue   # the site's status sentence, not part of the problem statement
            stmt.append(l)
        else:
            if re.match(r"^[a-z][a-z /\-]+\|?$", l) and len(l) < 40:   # tag lines like "number theory |"
                tags.append(l.strip(" |"))
                continue
            disc.append(l)
    statement = " ".join(stmt).strip()
    discussion = "\n".join(disc).strip()
    m = re.search(r"Comments \((\d+)\)", t)
    low = (statement + " " + discussion).lower()
    flags = [w for w in ("presumably", "not clear", "unclear", "ambiguous", "typo", "misstated", "not recorded", "trivial")
             if w in low]
    return {"status_line": status_line, "statement": statement, "discussion": discussion, "tags": tags,
            "comments": int(m.group(1)) if m else None, "flags": flags,
            "formalised": "Formalised statement?\n Yes" in t or "Formalised statement? Yes" in t}


def cmd_scout(args) -> int:
    try:
        import yaml
    except ImportError:
        print("scout needs PyYAML (pip install pyyaml)"); return 1
    db = Path(args.db) if args.db else ensure_erdos_db()
    P = yaml.safe_load(open(db))
    want_tags = {t.strip().lower() for t in args.tags.split(",") if t.strip()}
    cands = []
    for p in P:
        st = (p.get("status") or {}).get("state", "")
        if (p.get("prize") or "no") != "no":
            continue
        tags = {t.lower() for t in (p.get("tags") or [])}
        if not (tags & want_tags):
            continue   # target areas only (number theory / additive combinatorics / combinatorics by default)
        if st in ("falsifiable", "verifiable", "decidable"):
            cls = st
        elif st == "open":
            cls = "open"
        else:
            continue
        cands.append((str(p["number"]), cls, sorted(tags)))
    print(f"scout: {len(cands)} candidates ({sum(1 for c in cands if c[1] != 'open')} finite-computation classes, "
          f"{sum(1 for c in cands if c[1] == 'open')} open with target tags); fetching up to {args.fetch_limit} pages…", flush=True)
    rows = []
    for i, (n, cls, tags) in enumerate(cands):
        if i >= args.fetch_limit:
            break
        try:
            info = parse_problem_page(fetch_problem_page(n))
        except Exception as e:   # noqa: BLE001
            print(f"  #{n}: fetch/parse failed: {e}", flush=True)
            continue
        if not info["statement"]:
            continue
        L = len(info["statement"])
        score = {"decidable": 3.0, "falsifiable": 2.5, "verifiable": 2.5, "open": 1.0}[cls]
        score += 1.5 if info["flags"] else 0
        score += 1.0 if L <= 250 else 0.5 if L <= 400 else -0.5 if L > 700 else 0
        c = info["comments"] if info["comments"] is not None else 5
        score += 1.0 if c == 0 else 0.5 if c <= 2 else -1.0 if c > 5 else 0
        score += 0.5 if (set(tags) & want_tags) else 0
        rows.append({"n": n, "class": cls, "score": round(score, 2), "len": L, "comments": c, "flags": info["flags"],
                     "tags": tags, "statement": info["statement"], "discussion": info["discussion"],
                     "status_line": info["status_line"]})
    rows.sort(key=lambda r: -r["score"])
    written = []
    for r in rows[:args.top]:
        path = ROOT / "problems" / f"erdos_{r['n']}.json"
        if path.exists() and not args.overwrite:
            continue
        notes = (f"OPEN problem (site class: {r['class']}; status line: '{r['status_line']}'). Nothing is resolved: the harness "
                 f"must formalize the question's conjectured direction and its negation (--open) and prove whichever it can. "
                 f"Site discussion (verbatim, no proof hints added): {r['discussion'][:3500]}")
        json.dump({"id": r["n"], "statement": r["statement"], "status": f"{r['status_line']} (open; class {r['class']})",
                   "notes": notes, "url": f"https://www.erdosproblems.com/{r['n']}", "open": True, "class": r["class"],
                   "tags": r["tags"], "comments": r["comments"], "flags": r["flags"]},
                  open(path, "w"), indent=2, ensure_ascii=False)
        written.append(r["n"])
    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    rep = [f"# scout {ts}", "", f"database: {db}", f"candidates fetched: {len(rows)}; problem files written: {written}", "",
           "| # | class | score | len | comments | flags | tags | statement |", "|---|---|---|---|---|---|---|---|"]
    for r in rows[:60]:
        rep.append(f"| {r['n']} | {r['class']} | {r['score']} | {r['len']} | {r['comments']} | {','.join(r['flags'])} | "
                   f"{', '.join(r['tags'][:3])} | {r['statement'][:160].replace('|', '/')} |")
    (RUNS / f"scout-{ts}.md").write_text("\n".join(rep) + "\n")
    print("\n".join(rep[:25]))
    print(f"scout: report runs/scout-{ts}.md; wrote {len(written)} problem files: {written}")
    return 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "campaign":
        from campaign import main as campaign_main
        return campaign_main(sys.argv[2:])
    ap = argparse.ArgumentParser(description="LLM + Lean 4 harness for Erdős problems")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("campaign", help="dependency-aware research campaigns; use campaign --help")
    runp = sub.add_parser("run")
    runp.add_argument("--problem", required=True)
    runp.add_argument("--backend", choices=["claude-cli", "codex-cli", "file"], default="claude-cli")
    runp.add_argument("--model", default=None, help="model for claude-cli backend")
    runp.add_argument("--samples", type=int, default=3, help="attempts requested per proving round")
    runp.add_argument("--rounds", type=int, default=6, help="max proving rounds before decomposition")
    runp.add_argument("--decompose-rounds", type=int, default=10, help="refinement budget after decomposition")
    runp.add_argument("--skip-literature", action="store_true")
    runp.add_argument("--resume", default=None, help="existing run dir to resume")
    runp.add_argument("--lean-timeout", type=int, default=420)
    runp.add_argument("--llm-timeout", type=int, default=3600)
    runp.add_argument("--call-budget", type=float, default=8.0, help="max USD per proof-search claude -p call")
    runp.add_argument("--aux-budget", type=float, default=2.5, help="max USD per literature/judge call")
    runp.add_argument("--formal-budget", type=float, default=4.0, help="max USD per formalize/crosscheck call")
    runp.add_argument("--effort-aux", default="medium", choices=["low", "medium", "high", "xhigh", "max"],
                      help="claude effort for literature/backtranslate/faithful (measured: default effort spent $6.52 on one literature summary)")
    runp.add_argument("--effort-formal", default="high", choices=["low", "medium", "high", "xhigh", "max"])
    runp.add_argument("--effort-prove", default=None, choices=["low", "medium", "high", "xhigh", "max"],
                      help="claude effort for prove/decompose/refine/agentic (default: CLI default)")
    runp.add_argument("--agentic", choices=["off", "escalate", "always"], default="escalate",
                      help="sandboxed compile-loop attempts: never / after --agentic-after plain rounds / every round")
    runp.add_argument("--agentic-after", type=int, default=1, help="plain (one-shot) rounds before agentic rounds")
    runp.add_argument("--agentic-samples", type=int, default=3, help="parallel agentic attempts per round")
    runp.add_argument("--agentic-turns", type=int, default=80, help="max tool calls per agentic attempt")
    runp.add_argument("--run-budget", type=float, default=None, help="stop cleanly (exit 2) once this run's logged spend reaches N USD")
    runp.add_argument("--skip-assess", action="store_true", help="skip the triage stage (route = fast)")
    runp.add_argument("--mode", choices=["fast", "search-first", "construct", "research"], default=None,
                      help="override the triage routing decision")
    runp.add_argument("--stop-after", choices=["assess", "search", "construct"], default=None, help="stop after this stage (for routing/search regressions)")
    runp.add_argument("--search", choices=["auto", "always", "off"], default="auto",
                      help="bounded Python witness/counterexample search: auto = when triage routes search-first")
    runp.add_argument("--search-seconds", type=int, default=90, help="wall-clock cap for the search script")
    runp.add_argument("--open", action="store_true", help="open-problem mode: formalize and attack BOTH the conjecture and its negation")
    runp.add_argument("--allow-construct", action="store_true", help="enable the construction search for extremal/bound targets")
    runp.add_argument("--construct-budget", type=float, default=10.0, help="USD cap for the construction search")
    runp.add_argument("--construct-iters", type=int, default=4, help="construction search: model-proposed program variants")
    runp.add_argument("--construct-seconds", type=int, default=120, help="construction search: local-search seconds per iteration")
    runp.add_argument("--construct-wall", type=int, default=1800, help="construction search: total wall-clock cap (s)")
    runp.add_argument("--allow-research", action="store_true", help="enable the persistent research program for open research-depth targets (needs --run-budget)")
    runp.add_argument("--research-cycles", type=int, default=2, help="research program: cycles per invocation")
    runp.add_argument("--review-every", type=int, default=2, help="research program: write REVIEW.md every k cycles")
    runp.add_argument("--review-wait", type=int, default=0, help="research program: seconds to wait for human direction via the file backend (0 = stop)")
    runp.add_argument("--models", default=None, help="comma-separated model ids rotated across agentic attempts from round 2 (ensembles)")
    runp.add_argument("--literature-web", action="store_true", help="give the literature stage WebSearch/WebFetch (erdosproblems.com, forum, arXiv)")
    runp.add_argument("--web-budget", type=float, default=3.0, help="USD cap for the web-enabled literature call")
    runp.add_argument("--subgoal-prover", default=None, help="module:function implementing prove(goal, timeout) -> proof|None for isolated sorry goals")
    runp.add_argument("--no-cascade", action="store_true", help="disable the free specialist tactic cascade on sorry holes (ablation)")

    chk = sub.add_parser("check")
    chk.add_argument("file")
    chk.add_argument("--lean-timeout", type=int, default=420)

    rp = sub.add_parser("retrospect", help="learn playbook entries + harvest lemmas from a finished run")
    rp.add_argument("run_dir")
    rp.add_argument("--model", default=None)
    rp.add_argument("--backend", choices=["claude-cli", "codex-cli"], default="claude-cli")

    rg = sub.add_parser("regress", help="recompile every verified proof (fast); --full re-runs the pipeline")
    rg.add_argument("--full", action="store_true")
    rg.add_argument("--only", nargs="+", help="limit saved-proof replay to these problem IDs")
    rg.add_argument("--references", action="store_true", help="also check attributed reference-assisted fixtures")
    rg.add_argument("--problems", nargs="*", default=[])
    rg.add_argument("--rounds", type=int, default=3)
    rg.add_argument("--decompose-rounds", type=int, default=5)
    rg.add_argument("--agentic", default=None)
    rg.add_argument("--lean-timeout", type=int, default=420)

    sc = sub.add_parser("scout", help="rank OPEN problems (falsifiable/verifiable/decidable, no prize, target tags) and write problem files")
    sc.add_argument("--db", default=None, help="path to teorth/erdosproblems data/problems.yaml (default: clone into runs/.cache)")
    sc.add_argument("--tags", default="number theory,additive combinatorics,combinatorics")
    sc.add_argument("--top", type=int, default=15)
    sc.add_argument("--fetch-limit", type=int, default=400)
    sc.add_argument("--overwrite", action="store_true")

    im = sub.add_parser("improve", help="self-improvement loop: run → retrospect → regress, per cycle")
    im.add_argument("--problems", nargs="+", required=True)
    im.add_argument("--cycles", type=int, default=1)
    im.add_argument("--rounds", type=int, default=3)
    im.add_argument("--decompose-rounds", type=int, default=5)
    im.add_argument("--agentic", default="off")
    im.add_argument("--eval-problems", nargs="+", required=True, help="held-out IDs, disjoint from training problems")
    im.add_argument("--backend", choices=["claude-cli", "codex-cli"], default="claude-cli",
                    help="claude-cli is the default; codex-cli needs the `codex` CLI on PATH")
    im.add_argument("--model", default=None)

    args = ap.parse_args()
    if args.cmd == "check":
        checker = LeanChecker(FORMAL, args.lean_timeout)
        res = checker.check(Path(args.file).read_text(), RUNS / "adhoc" / Path(args.file).name)
        print(json.dumps(res, indent=2))
        return 0 if res["ok"] else 1
    if args.cmd == "retrospect":
        return cmd_retrospect(args)
    if args.cmd == "regress":
        return cmd_regress(args)
    if args.cmd == "improve":
        return cmd_improve(args)
    if args.cmd == "scout":
        return cmd_scout(args)
    return Harness(args).run()


if __name__ == "__main__":
    sys.exit(main())
