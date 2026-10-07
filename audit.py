#!/usr/bin/env python3
"""Audit a verified proof mechanically, so that `verified=True` can stand without a human reading the proof.

    python3 audit.py --run runs/<ts>-timesplit-erdos<alias>           # Lean checks + provenance + blindness
    python3 audit.py --run runs/<ts>-erdos<n> --no-benchmark          # Lean checks only (no time-split item)

Writes <run>/AUDIT.json and <run>/AUDIT.md and exits 0 only on PASS. No model calls anywhere in this file.

Why each check exists. The harness's own final verification compiles the proof, prints its axioms and checks
that the frozen statement's TEXT appears verbatim. Text is not meaning: a line before the frozen theorem such as
`instance : LT ℕ := ⟨fun _ _ => True⟩`, an `open` that changes name resolution, or a macro, can make the same
characters elaborate to a different, easier proposition, and every text check still passes.
`tests/test_audit.py` shows the instance attack getting past a text match. So the audit compares ELABORATED
terms: the proved constant's type, and every definition the frozen statement defines, hashed structurally in the
proof's environment and in a clean elaboration of the frozen statement alone. Around that:
  - kernel replay: `leanchecker` re-checks every declaration of the compiled proof through the kernel;
  - axioms: exactly Lean's three standard axioms, nothing that trusts compiled code (`native_decide`);
  - source scan: no `sorry`, no kernel bypass (`debug.skipKernelTC`), no metaprogramming that runs code at
    elaboration time (`run_cmd`, `#eval`, `elab`, `macro`, `syntax`, `initialize`), which could add declarations
    the kernel never sees;
  - imports: only Mathlib, the frozen statement's own imports and the repo's `Formal.Library`. A per-run module
    could carry an instance that changes both elaborations at once, and then the comparison proves nothing.
For a time-split benchmark item it also checks:
  - provenance: the frozen statement is the benchmark's, which is formal-conjectures' main theorem with
    `answer(...)` stripped, and the proved direction agrees with the recorded answer;
  - blindness: the probe did not recall the result, the run was masked and ran under `--benchmark`, and no
    prompt the run sent names the problem.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, os, re, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formal"
AUDIT_DIR = FORMAL / ".lake" / "audit"          # `lean -o` only writes oleans for sources under the Lean root
POOL = ROOT / "benchmarks" / "timesplit" / "pool.json"
RESULTS = ROOT / "benchmarks" / "timesplit" / "results"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TRUSTED_IMPORT_PREFIXES = ("Mathlib", "Formal.Library")
LEAN_TIMEOUT = 1800

# (label, pattern) over the proof with comments removed. Each is a way to make Lean accept something the kernel
# never checked, or to smuggle one in.
FORBIDDEN = [
    ("sorry/admit", r"\b(sorry|admit)\b"),
    ("native_decide / compiled-code trust", r"\bnative_decide\b|ofReduceBool|ofReduceNat|Lean\.reduceBool"),
    ("implemented_by / extern", r"implemented_by|@\[\s*extern\b|\bextern\b"),
    ("unsafe", r"\bunsafe\b"),
    ("axiom / opaque declaration", r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:axiom|opaque|constant)\b"),
    ("kernel bypass option", r"debug\.skipKernelTC|\bskipKernelTC\b"),
    ("elaboration-time code", r"\brun_cmd\b|\brun_elab\b|\brun_meta\b|\brun_tac\b|#eval\b|#exit\b"),
    # A NEW tactic keyword (`elab "prove_search46" : tactic => ...`, the certificate tactic of a Bool-reflected
    # search) is allowed: it can only run where a proof invokes it, the term it builds is kernel-checked, and the
    # kernel replay re-checks any declaration it adds. Everything that can hook EXISTING syntax is not:
    # elab_rules/macro_rules, syntax extensions, and command/term elaborators, any of which could reinterpret the
    # frozen statement or this audit's own `#print axioms`.
    ("new syntax / elaborators", r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:local\s+|scoped\s+)?"
                                 r"(?:elab_rules|macro_rules|syntax|declare_syntax_cat"
                                 r"|(?:elab|macro)\b(?!\s+\"[A-Za-z_][A-Za-z0-9_']*\"\s*:\s*tactic\b))\b"),
    ("elaborator attributes", r"@\[\s*(?:command_elab|term_elab|tactic|builtin_\w+|macro)\b"),
    ("initializers", r"\b(?:builtin_)?initialize\b"),
    ("environment manipulation", r"\baddDecl\b|Environment\.|\bKernel\.|\bmodifyEnv\b|\bsetEnv\b"),
]


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def strip_comments(src: str) -> str:
    """Remove `--` line comments and (nested) `/- -/` block comments, keeping string literals intact."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src[i] == '"':                      # a string literal: copy it through verbatim
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def forbidden_constructs(src: str) -> list[str]:
    body = strip_comments(src)
    return [label for label, pat in FORBIDDEN if re.search(pat, body)]


def import_lines(src: str) -> list[str]:
    return re.findall(r"(?m)^import\s+(\S+)", src)


def strip_imports(src: str) -> str:
    return re.sub(r"(?m)^import\s+\S+\s*\n", "", src)


def frozen_names(frozen: str) -> tuple[str | None, list[str]]:
    """The frozen theorem's name and the names the frozen statement defines itself, FULLY QUALIFIED: a `def` inside
    `namespace Finset ... end Finset` is the constant `Finset.lcmInterval` (train #678's statement), and looking up
    the bare name finds nothing in either elaboration."""
    body = strip_comments(frozen)
    stack: list[tuple[str, str]] = []                     # ("namespace" | "section", name)
    thms, defs = [], []
    decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
                      r"(theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s:({\[]+)")
    for line in body.splitlines():
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            stack.append(("namespace", m.group(1)))
            continue
        m = re.match(r"(?:noncomputable\s+)?section\b\s*(\S*)", s)
        if m and not s.startswith("section_"):
            stack.append(("section", m.group(1)))
            continue
        m = re.match(r"end\b\s*(\S*)", s)
        if m and stack:
            stack.pop()
            continue
        m = decl.match(line)
        if m:
            kind, name = m.group(1), m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = ".".join(n for k, n in stack if k == "namespace" and n)
                full = f"{prefix}.{name}" if prefix else name
            (thms if kind in ("theorem", "lemma") else defs).append(full)
    return (thms[-1] if thms else None), defs


def dump_code(roots: list[tuple[str, bool]]) -> str:
    """Lean that prints a structural fingerprint of each root constant and of every constant DEFINED IN THIS FILE
    that it reaches: kind, universe parameters, and hashes of its type and (when followed) its value. The proved
    theorem is a root whose value is NOT followed (its proof may use anything); definitions are followed."""
    items = ", ".join(f"(`{n}, {'true' if follow else 'false'})" for n, follow in roots)
    return f"""
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo : List (Name × Bool) := [{items}]
  let mut seen : NameSet := {{}}
  let mut lines : Array String := #[]
  for _ in [0:100000] do
    match todo with
    | [] => break
    | (n, follow) :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => lines := lines.push s!"AUDIT-DUMP {{n}} MISSING"
      | some ci =>
        let kind := match ci with
          | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
        let v := if follow then ci.value? else none
        lines := lines.push s!"AUDIT-DUMP {{n}} KIND {{kind}} LEVELS {{ci.levelParams}} TYPE {{ci.type.hash}} VALUE {{v.map Expr.hash}}"
        let deps := ci.type.getUsedConstants ++ ((v.map Expr.getUsedConstants).getD #[])
        for d in deps do
          if (env.getModuleIdxFor? d).isNone && !seen.contains d then
            todo := (d, true) :: todo
  for l in lines do IO.println l
"""


def run_lean(path: Path, timeout: int = LEAN_TIMEOUT) -> tuple[int, str]:
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=FORMAL, capture_output=True, text=True,
                           timeout=timeout)
        return r.returncode, (r.stdout or "") + (r.stderr or "")
    except subprocess.TimeoutExpired:
        return 124, f"timed out after {timeout}s"


def lean_errors(out: str) -> list[str]:
    return [l for l in out.splitlines() if re.search(r":\d+:\d+: error", l)]


def parse_dump(out: str) -> dict[str, str]:
    d = {}
    for l in out.splitlines():
        m = re.match(r"AUDIT-DUMP (\S+) (.*)$", l.strip())
        if m:
            d[m.group(1)] = m.group(2)
    return d


def parse_axioms(out: str, name: str) -> set[str] | None:
    m = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", out)
    if m:
        return {a.strip() for a in m.group(1).split(",") if a.strip()}
    if re.search(rf"'{re.escape(name)}' does not depend on any axioms", out):
        return set()
    return None


def kernel_replay(candidate: str, tag: str) -> dict:
    """Compile the proof to an .olean and re-check every declaration in it through the kernel with the
    toolchain's `leanchecker` (imports are trusted, the module itself is replayed)."""
    toolchain = (FORMAL / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    checker = Path.home() / ".elan" / "toolchains" / toolchain / "bin" / "leanchecker"
    if not checker.exists():
        return {"ok": None, "detail": f"leanchecker not found at {checker}"}
    mod = "AuditCand" + re.sub(r"\W", "", tag)
    d = AUDIT_DIR / tag
    (d / "olean").mkdir(parents=True, exist_ok=True)
    src = d / f"{mod}.lean"
    src.write_text(candidate)
    try:
        r = subprocess.run(["lake", "env", "lean", "-o", str(d / "olean" / f"{mod}.olean"), str(src)], cwd=FORMAL,
                           capture_output=True, text=True, timeout=LEAN_TIMEOUT)
        if r.returncode:
            return {"ok": False, "detail": "compiling to .olean failed: " + ((r.stdout or "") + (r.stderr or ""))[-400:]}
        lp = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=FORMAL, capture_output=True, text=True).stdout.strip()
        env = {**os.environ, "LEAN_PATH": f"{d / 'olean'}:{lp}"}
        r = subprocess.run([str(checker), mod], cwd=FORMAL, capture_output=True, text=True, env=env, timeout=LEAN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"ok": False, "detail": "timed out"}
    out = ((r.stdout or "") + (r.stderr or "")).strip()
    return {"ok": r.returncode == 0 and "error" not in out.lower(), "detail": out[-400:] or "all declarations replayed"}


# ---------------------------------------------------------------- the Lean checks ------------------------------

def lean_checks(candidate: str, frozen: str, frozen_imports: list[str], tag: str) -> dict:
    checks: dict[str, dict] = {}
    main, defs = frozen_names(frozen)
    if not main:
        return {"frozen_statement": {"ok": False, "detail": "no theorem in the frozen statement"}}
    bad = forbidden_constructs(candidate)
    checks["source_scan"] = {"ok": not bad, "detail": ", ".join(bad) or "no sorry, kernel bypass or elaboration-time code"}
    imps = import_lines(candidate)
    untrusted = [m for m in imps if not (m.startswith(TRUSTED_IMPORT_PREFIXES) or m in frozen_imports)]
    checks["imports"] = {"ok": not untrusted, "detail": ("untrusted: " + ", ".join(untrusted)) if untrusted
                         else f"{len(imps)} import(s), all Mathlib, Formal.Library or the statement's own"}
    d = AUDIT_DIR / tag
    d.mkdir(parents=True, exist_ok=True)
    roots = [(n, True) for n in defs] + [(main, False)]
    # 1. the proof itself, fresh: compiles, and its axioms, and its fingerprints
    cand_file = d / "Candidate.lean"
    cand_file.write_text(candidate.rstrip() + "\n" + dump_code(roots) + f"\n#print axioms {main}\n")
    rc, out = run_lean(cand_file)
    errs = lean_errors(out)
    checks["compiles"] = {"ok": rc == 0 and not errs, "detail": (errs[:2] and "; ".join(errs[:2])[:300]) or "no errors"}
    sorry_warn = [l for l in out.splitlines() if "declaration uses 'sorry'" in l]
    checks["no_sorry_warning"] = {"ok": not sorry_warn, "detail": f"{len(sorry_warn)} sorry warning(s)"}
    ax = parse_axioms(out, main)
    checks["axioms"] = {"ok": ax is not None and ax <= STD_AXIOMS,
                        "detail": "unreadable" if ax is None else ("[" + ", ".join(sorted(ax)) + "]")}
    cand_dump = parse_dump(out)
    # 2. the frozen statement alone, under the proof's imports: the meaning the proof is supposed to prove
    ref_imports = list(dict.fromkeys(imps + frozen_imports))
    ref_file = d / "Reference.lean"
    ref_file.write_text("".join(f"import {m}\n" for m in ref_imports) + "\n" + strip_imports(frozen).strip()
                        + "\n" + dump_code(roots))
    rrc, rout = run_lean(ref_file)
    ref_dump = parse_dump(rout)
    rerrs = lean_errors(rout)
    same = bool(ref_dump) and ref_dump == cand_dump and all("MISSING" not in v for v in ref_dump.values())
    diff = sorted(k for k in set(ref_dump) | set(cand_dump) if ref_dump.get(k) != cand_dump.get(k))
    kind_ok = (cand_dump.get(main) or "").startswith("KIND theorem")
    checks["statement_identity"] = {
        "ok": same and kind_ok and not rerrs,
        "detail": (f"the proved `{main}` and {len(defs)} frozen definition(s) are structurally identical to a clean "
                   f"elaboration of the frozen statement ({len(ref_dump)} constant(s) compared)") if same and kind_ok
        else ("reference did not elaborate: " + "; ".join(rerrs[:1])[:200] if rerrs
              else (f"missing in the frozen elaboration: {', '.join(k for k, v in ref_dump.items() if 'MISSING' in v)}"
                    if any("MISSING" in v for v in ref_dump.values()) else
                    f"differs at: {', '.join(diff[:6]) or '(no fingerprints)'}") + ("" if kind_ok else f"; `{main}` is not a theorem"))}
    # 3. kernel replay of the proof as written
    checks["kernel_replay"] = kernel_replay(candidate, tag)
    # 4. Comparator (and nanoda), when installed: an independent statement match and an independent kernel
    checks.update(comparator_checks(candidate, frozen, tag))
    return checks


# ---------------------------------------------------------------- independent checkers (2026-10-07) -------------
# leanprover/comparator checks that a proof proves exactly a separately written challenge statement, using no axiom
# beyond the permitted ones, through the Lean kernel; with nanoda (ammkrn/nanoda_lib) also through an independent kernel.
# openai/math verifies its 405 Lean results this way. tools/install.sh builds all of it. On macOS there is no Landlock,
# so Comparator runs under its own fake-landrun shim, without its sandbox. The source scan already bans the
# elaboration-time code the sandbox guards against, and the detail says the sandbox was absent.
TOOLS = ROOT / "tools"


def comparator_tools() -> dict | None:
    """Paths to comparator, lean4export, landrun (real or the macOS shim) and nanoda, or None if comparator is missing."""
    env = os.environ
    comp = Path(env.get("COMPARATOR_BIN") or TOOLS / "comparator" / ".lake" / "build" / "bin" / "comparator")
    export = Path(env.get("COMPARATOR_LEAN4EXPORT") or TOOLS / "lean4export" / ".lake" / "build" / "bin" / "lean4export")
    if not (comp.exists() and export.exists()):
        return None
    landrun = env.get("COMPARATOR_LANDRUN") or (shutil_which("landrun") or str(TOOLS / "landrun"))
    nanoda = Path(env.get("COMPARATOR_NANODA") or TOOLS / "nanoda_lib" / "target" / "release" / "nanoda_bin")
    return {"comparator": str(comp), "lean4export": str(export), "landrun": landrun,
            "nanoda": str(nanoda) if nanoda.exists() else None,
            "sandbox": "landrun" if Path(landrun).name == "landrun" and Path(landrun).parent != TOOLS else "none (fake-landrun shim)"}


def shutil_which(name: str) -> str | None:
    import shutil
    return shutil.which(name)


def header_lines(src: str) -> list[str]:
    """The leading `import` / `set_option` / `open` lines (and blanks) of a Lean file."""
    out = []
    for line in src.splitlines():
        if line.startswith(("import ", "set_option ", "open ")) or not line.strip():
            out.append(line)
        else:
            break
    return out


def comparator_files(candidate: str, frozen: str, main: str, defs: list[str], base: str) -> tuple[str, str, dict]:
    """The challenge module (the frozen statement under the proof's own header), the solution module (the proof) and
    Comparator's config, for module prefix `base`."""
    challenge = "\n".join(header_lines(candidate)).rstrip() + "\n\n" + strip_imports(frozen).strip() + "\n"
    cfg = {"challenge_module": f"{base}.Challenge", "solution_module": f"{base}.Solution", "theorem_names": [main],
           "definition_names": list(defs), "permitted_axioms": sorted(STD_AXIOMS)}
    return challenge, candidate, cfg


def comparator_checks(candidate: str, frozen: str, tag: str) -> dict:
    """`comparator` and, when nanoda is built, `nanoda`. Empty when Comparator is not installed, so a machine without
    the tools keeps the audit it had."""
    tools = comparator_tools()
    main, defs = frozen_names(frozen)
    if tools is None or not main:
        return {}
    base = "Formal.Audit.A" + hashlib.sha1(tag.encode()).hexdigest()[:12]
    d = FORMAL / Path(*base.split("."))
    d.mkdir(parents=True, exist_ok=True)
    challenge, solution, cfg = comparator_files(candidate, frozen, main, defs, base)
    if tools["nanoda"]:
        cfg["enable_nanoda"] = True
    (d / "Challenge.lean").write_text(challenge)
    (d / "Solution.lean").write_text(solution)
    (d / "config.json").write_text(json.dumps(cfg, indent=1))
    env = {**os.environ, "COMPARATOR_LANDRUN": tools["landrun"], "COMPARATOR_LEAN4EXPORT": tools["lean4export"],
           **({"COMPARATOR_NANODA": tools["nanoda"]} if tools["nanoda"] else {})}
    try:
        r = subprocess.run(["lake", "env", tools["comparator"], str(d / "config.json")], cwd=FORMAL, capture_output=True,
                           text=True, timeout=LEAN_TIMEOUT, env=env)
        out = ((r.stdout or "") + "\n" + (r.stderr or "")).replace("WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING", "")
        rc = r.returncode
    except subprocess.TimeoutExpired:
        out, rc = "timed out", -1
    finally:
        for f in ("Challenge.lean", "Solution.lean", "config.json"):
            try:
                (d / f).unlink()
            except OSError:
                pass
    ok = rc == 0 and "Your solution is okay!" in out
    tail = " ".join(l.strip() for l in out.splitlines() if l.strip() and not l.startswith(("warning:", "Note:", "✔", "⚠")))[-400:]
    checks = {"comparator": {"ok": ok, "detail": (f"the proof matches the challenge statement ({len(defs)} definition(s) "
                                                  f"compared), on the permitted axioms, through the Lean kernel; sandbox: "
                                                  f"{tools['sandbox']}") if ok else f"rejected: {tail}"}}
    if tools["nanoda"]:
        acc = "nanoda kernel accepts the solution" in out
        checks["nanoda"] = {"ok": acc, "detail": "the independent nanoda kernel accepts the proof" if acc
                            else ("not reached: Comparator stopped earlier" if not ok and "nanoda" not in out else f"rejected: {tail}")}
    return checks


# ---------------------------------------------------------------- benchmark provenance and blindness ----------

def pool_item(problem: str) -> dict | None:
    if not POOL.exists():
        return None
    pool = json.loads(POOL.read_text())
    items = pool["items"] if isinstance(pool, dict) and "items" in pool else pool
    return next((i for i in items if str(i.get("problem")) == str(problem)), None)


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def result_record(run_dir: Path) -> tuple[str | None, dict | None]:
    """The time-split record that points at this run directory, and its tag."""
    rel = str(run_dir.resolve().relative_to(ROOT)) if run_dir.resolve().is_relative_to(ROOT) else str(run_dir)
    for f in sorted(RESULTS.glob("*.jsonl")):
        if any(x in f.name for x in (".infra.", ".ideas.", ".progress.", ".aliases.")):
            continue
        for l in f.read_text().splitlines():
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if r.get("run_dir") == rel:
                return f.name[: -len(".jsonl")], r
    return None, None


def prompts_of(run_dir: Path, alias: str | None) -> list[tuple[str, str, str]]:
    """(file, prompt, response) for every model call of the run, its direction children and its research sub-runs.
    Transcripts store the prompt after the masking scrub, i.e. exactly what the model saw; agentic sessions'
    TASK.md files are included as prompts."""
    files = glob.glob(str(run_dir / "**" / "transcripts" / "*.md"), recursive=True)
    if alias:
        files += glob.glob(str(ROOT / "programs" / f"erdos_{alias}" / "**" / "transcripts" / "*.md"), recursive=True)
    out = []
    for f in sorted(set(files)):
        t = Path(f).read_text(errors="replace")
        head, _, resp = t.partition("\n## response\n")
        out.append((f, head, resp))
    tasks = glob.glob(str(run_dir / "**" / "TASK.md"), recursive=True)
    if alias:
        tasks += glob.glob(str(ROOT / "programs" / f"erdos_{alias}" / "**" / "TASK.md"), recursive=True)
    for f in sorted(set(tasks)):
        out.append((f, Path(f).read_text(errors="replace"), ""))
    return out


def identity_patterns(item: dict) -> list[tuple[str, str]]:
    n = re.escape(str(item["problem"]))
    pats = [("problem number with context", rf"(?i)(#\s*{n}\b|problem\s*{n}\b|erd[őo]s\S*\s*#?\s*{n}\b|/{n}\b)"),
            # a named result ("Erdős–Ko–Rado") is kept by the mask on purpose; the bare name is the leak
            ("Erdős by name", r"(?i)erd[őo]s(?![–\-\w])|erdosproblems")]
    blob = json.dumps({k: item.get(k) for k in ("evidence", "resolution_sentences", "first_public_source", "ai_wiki",
                                                   "provenance")}, ensure_ascii=False)
    for a in sorted(set(re.findall(r"\b\d{4}\.\d{4,5}\b", blob))):
        pats.append((f"resolution arXiv id", re.escape(a)))
    return pats


def negated(statement: str) -> str:
    """The benchmark's own negation of a frozen statement (the NO direction's target)."""
    sys.path.insert(0, str(ROOT / "benchmarks" / "timesplit"))
    import timesplit                                         # stdlib-only at import time
    return timesplit.negated_statement(statement)


def benchmark_checks(run_dir: Path, state: dict, frozen: str, direction: str | None) -> tuple[dict, dict]:
    tag, rec = result_record(run_dir)
    info: dict = {"tag": tag}
    if not rec:
        return {"benchmark_record": {"ok": False, "detail": "no time-split record points at this run"}}, info
    item = pool_item(rec["problem"])
    info.update({"problem": rec["problem"], "split": rec.get("split"), "alias": rec.get("alias")})
    checks: dict[str, dict] = {}
    # provenance: the audited statement is the benchmark's statement (YES direction) or its negation (NO)
    mask = {}
    mf = ROOT / ((item or {}).get("mask") or {}).get("file", "")
    if item and mf.is_file():
        mask = json.loads(mf.read_text())
    ref = mask.get("statement_lean") or ""
    direction = direction or rec.get("committed") or "pos"
    if ref and direction == "neg":
        try:
            ref = negated(ref)
        except ValueError:
            ref = ""
    same = bool(ref) and norm(re.sub(r"erdos_\d+", "X", ref)) == norm(re.sub(r"erdos_\d+", "X", frozen))
    checks["provenance"] = {"ok": same, "detail": (f"the {direction} direction of the benchmark's statement "
                                                   f"({mask.get('source', '?')})" if same
                                                   else f"frozen statement differs from the benchmark's ({direction})")}
    answer = (item or {}).get("answer")
    agrees = direction == ("pos" if answer in (True, "yes", "true") else "neg")
    checks["direction_matches_answer"] = {"ok": agrees,
                                          "detail": f"proved {direction}, recorded answer {answer} "
                                                    f"({(item or {}).get('answer_source', '?')})"
                                                    + ("" if agrees else ": a CONTRADICTION to re-audit, never a solve")}
    faithful = ((state.get("verify") or {}).get("faithful") or {}).get("faithful")
    checks["faithfulness_judges"] = {"ok": bool(faithful) and bool(((item or {}).get("mask") or {}).get("faithful")),
                                     "detail": f"at build: {((item or {}).get('mask') or {}).get('faithful')}; "
                                               f"at verification: {faithful}"}
    # blindness
    probe = ((item or {}).get("probe") or {}).get("verdict")
    checks["probe"] = {"ok": probe in ("unaware", "misremembered"), "detail": f"probe verdict: {probe}"}
    proto = rec.get("protocol") or {}
    checks["masked_benchmark_run"] = {"ok": bool(proto.get("masked")) and bool(state.get("benchmark")),
                                      "detail": f"masked={proto.get('masked')}, --benchmark={bool(state.get('benchmark'))}, "
                                                f"knowledge={proto.get('knowledge')}"}
    calls = prompts_of(run_dir, str(rec.get("alias") or ""))
    if rec.get("engine_run"):
        # a Lean stage whose blueprint is a research-engine proof (experiments/idea-engine-2026-10-02/hardsteps_lean.py)
        # is blind only if the engine run that wrote the proof was: its prompts are scanned too, and its responses
        # count toward `responses_naming_the_problem`
        info["engine_run"] = rec["engine_run"]
        calls += prompts_of(ROOT / rec["engine_run"], str(rec.get("engine_alias") or ""))
    hits, recall = {}, {}
    for label, pat in identity_patterns(item or {"problem": rec["problem"]}):
        hits[label] = sum(1 for _, p, _ in calls if re.search(pat, p))
        recall[label] = sum(1 for _, _, r in calls if re.search(pat, r))
    checks["no_identity_in_prompts"] = {"ok": bool(calls) and not any(hits.values()),
                                        "detail": f"{len(calls)} prompt(s) scanned; matches: {hits}"}
    info["responses_naming_the_problem"] = recall
    # replication: other verified runs of the same item on fresh aliases
    reps = []
    for f in sorted(RESULTS.glob("*.jsonl")):
        if any(x in f.name for x in (".infra.", ".ideas.", ".progress.", ".aliases.")):
            continue
        for l in f.read_text().splitlines():
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if str(r.get("problem")) == str(rec["problem"]) and r.get("solved") and r.get("run_dir") != rec.get("run_dir"):
                reps.append({"tag": f.name[:-6], "alias": r.get("alias"), "run_dir": r.get("run_dir")})
    info["other_verified_runs"] = reps
    return checks, info


# ---------------------------------------------------------------- driver ---------------------------------------

def proof_dirs(run_dir: Path) -> list[tuple[Path, str | None]]:
    """Where a run keeps its verified proof: `final/` at the root (a run committed to one direction, or a plain
    run), or `pos/final` / `neg/final` for an --open run, whose directions keep their own state."""
    if (run_dir / "final").is_dir():
        return [(run_dir, None)]
    return [(run_dir / d, d) for d in ("pos", "neg") if (run_dir / d / "final").is_dir()]


def audit_one(run_dir: Path, sub: Path, direction: str | None, benchmark: bool) -> dict:
    state = json.loads((sub / "state.json").read_text())
    finals = sorted((sub / "final").glob("*.lean"))
    rel = lambda p: str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p)
    report: dict = {"run": rel(sub), "at": now(), "direction": direction}
    if len(finals) != 1:
        report.update({"verdict": "FAIL", "checks": {"final_proof": {"ok": False, "detail": f"{len(finals)} file(s) in final/"}}})
        return report
    candidate = finals[0].read_text()
    frozen = state.get("statement") or ""
    pfile = next((p for p in (sub / "problem.json", run_dir / "problem.json") if p.exists()), None)
    problem = json.loads(pfile.read_text()) if pfile else {}
    frozen_imports = [m for m in (problem.get("imports") or []) if isinstance(m, str)]
    tag = (run_dir.name + (f"-{direction}" if direction else ""))[-44:]
    report["proof"] = {"file": rel(finals[0]), "sha256": hashlib.sha256(candidate.encode()).hexdigest()}
    checks = lean_checks(candidate, frozen, frozen_imports, tag)
    if benchmark:
        bchecks, info = benchmark_checks(run_dir, state, frozen, direction)
        checks.update(bchecks)
        report["benchmark"] = info
    report["checks"] = checks
    report["verdict"] = "PASS" if all(c.get("ok") is True for c in checks.values()) else "FAIL"
    return report


def audit(run_dir: Path, benchmark: bool = True) -> dict:
    """Audit every verified proof the run holds, write AUDIT.md/AUDIT.json beside each, and return the report of
    the first (the only one, except when both --open directions closed, which is itself a contradiction)."""
    run_dir = run_dir.resolve()
    dirs = proof_dirs(run_dir)
    if not dirs:
        return {"run": str(run_dir), "at": now(), "verdict": "FAIL",
                "checks": {"final_proof": {"ok": False, "detail": "no final/ proof in the run"}}}
    reports = []
    for sub, direction in dirs:
        r = audit_one(run_dir, sub, direction, benchmark)
        (sub / "AUDIT.json").write_text(json.dumps(r, indent=1, ensure_ascii=False) + "\n")
        (sub / "AUDIT.md").write_text(render_md(r))
        reports.append(r)
    return reports[0] if len(reports) == 1 else {**reports[0], "all": reports,
                                                 "verdict": "FAIL" if any(r["verdict"] != "PASS" for r in reports) else "PASS"}


def render_md(r: dict) -> str:
    lines = [f"# Audit: {r['verdict']}", "", f"- run: `{r['run']}`", f"- at: {r['at']}"]
    if r.get("proof"):
        lines.append(f"- proof: `{r['proof']['file']}` (sha256 {r['proof']['sha256'][:16]}…)")
    b = r.get("benchmark") or {}
    if b:
        lines.append(f"- benchmark: #{b.get('problem')} ({b.get('split')}), tag `{b.get('tag')}`, alias {b.get('alias')}")
    lines += ["", "| check | result | detail |", "|---|---|---|"]
    for k, c in r.get("checks", {}).items():
        ok = c.get("ok")
        lines.append(f"| {k} | {'pass' if ok is True else ('FAIL' if ok is False else 'unavailable')} | "
                     f"{str(c.get('detail', '')).replace('|', '/')} |")
    if b.get("other_verified_runs") is not None:
        lines += ["", f"Other verified runs of this item: {len(b['other_verified_runs'])}"
                  + "".join(f"\n- `{x['tag']}` alias {x['alias']}: `{x['run_dir']}`" for x in b["other_verified_runs"])]
    if b.get("responses_naming_the_problem") is not None:
        lines += ["", f"Model responses naming the problem (a recall signal, not a leak): {b['responses_naming_the_problem']}"]
    lines += ["", "PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard "
              "axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the "
              "benchmark's own and the run was blind by every check above. It certifies the proof, not the "
              "novelty: a reconstruction of a published result stays a reconstruction."]
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, action="append", help="run directory with final/<proof>.lean (repeatable)")
    ap.add_argument("--no-benchmark", action="store_true", help="skip the time-split provenance and blindness checks")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    worst = 0
    for rd in args.run:
        r = audit(Path(rd), benchmark=not args.no_benchmark)
        for one in r.get("all") or [r]:
            print(json.dumps(one, indent=1, ensure_ascii=False) if args.json else render_md(one))
        worst = max(worst, 0 if r["verdict"] == "PASS" else 1)
    return worst


if __name__ == "__main__":
    sys.exit(main())
