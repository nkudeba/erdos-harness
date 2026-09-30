#!/usr/bin/env python3
"""Keep the Erdős Atlas current on its own: re-rank, commit and deploy whenever its inputs change.

    python3 atlas_refresh.py             # refresh now if anything changed (what the publisher runs every cycle)
    python3 atlas_refresh.py --force     # re-rank, commit and deploy regardless of the timers
    python3 atlas_refresh.py --no-push   # commit locally, push nothing

The operator's rule (2026-09-30): the Atlas is updated whatever we do. The live publisher (`result_feed.py
watch`, a LaunchAgent) already sends run evidence and revised scores to the site every 30 seconds. What it did not
do was re-rank, so a run's mechanical evidence reached `rankings.json` only when someone ran the ranker. It also did
not commit or push the ranker's outputs, or refresh the site's baked snapshot. This module does all three. The
publisher calls `maybe_refresh()` after every sync, and nothing here makes a model call.

- **Re-rank** (`atlas-data/rank_problems.py`, about 3 s) when any input changed: a run's state, a recorded finding,
  a brief, a saved proof, benchmark results or evidence, the ranker's code. At most every RERANK_EVERY seconds.
- **Commit and push** the Atlas's own files in this repo, and nothing else, at most every COMMIT_EVERY seconds.
- **Deploy** the site by committing and pushing `erdos-atlas/app/data.json` to its repository, at most every
  DEPLOY_EVERY seconds. Between deploys the live overlay carries scores and runs.

Git safety: a repository is committed to only when it is on `main` with no merge, rebase or index lock in
progress. Only the listed paths are staged and committed (`git commit -- <paths>`), so anyone's other work in the
checkout is left alone. A push that fails, for example because the remote moved, is recorded and retried later,
never forced. The per-alias research-guidance files are never committed.
"""
from __future__ import annotations
import argparse, datetime as dt, hashlib, json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STATE = ROOT / ".result-feed" / "atlas-refresh.json"
SITE = ROOT / "erdos-atlas"
RERANK_EVERY, COMMIT_EVERY, DEPLOY_EVERY = 300, 900, 1800
HARNESS_PATHS = ["atlas-data/reviewed.json", "atlas-data/rankings.json", "atlas-data/rankings.csv",
                 "atlas-data/briefs", "atlas-data/predictions.jsonl"]
SITE_PATHS = ["app/data.json"]


def now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _stat(p: Path):
    try:
        s = p.stat()
        return (str(p), s.st_mtime_ns, s.st_size)
    except OSError:
        return (str(p), 0, 0)


def inputs_signature(root: Path = ROOT) -> str:
    """A hash over everything the ranker reads, by mtime and size, so an unchanged Atlas costs one directory walk."""
    files = [root / "atlas-data" / n for n in ("reviewed.json", "rank_problems.py", "parsed.json", "problems.yaml")]
    files += [root / "atlas_ids.py", root / "harness.py"]
    for pattern in ("atlas-data/briefs/*.md", "atlas-data/forum/*", "knowledge/solved/*", "benchmarks/timesplit/results/*.jsonl",
                    "benchmarks/timesplit/evidence/**/AUDIT.json", "benchmarks/deductive/masks/*.json",
                    "benchmarks/timesplit/masks/*.json"):
        files += sorted(root.glob(pattern))
    files += sorted((root / "runs").rglob("state.json")) if (root / "runs").is_dir() else []
    h = hashlib.sha256()
    for f in files:
        h.update(repr(_stat(f)).encode())
    return h.hexdigest()


def _git(repo: Path, *args, check=False, timeout=120) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True, timeout=timeout, check=check)


def commit_paths(repo: Path, paths: list[str], message: str) -> dict:
    """Commit exactly `paths` (their working-tree state) on main. Returns {"commit": sha} or {"skipped": why}."""
    if not (repo / ".git").exists():
        return {"skipped": "not a git repository"}
    gitdir = repo / ".git"
    for busy in ("MERGE_HEAD", "rebase-merge", "rebase-apply", "index.lock", "CHERRY_PICK_HEAD"):
        if (gitdir / busy).exists():
            return {"skipped": f"{busy} present"}
    branch = _git(repo, "symbolic-ref", "--short", "HEAD").stdout.strip()
    if branch != "main":
        return {"skipped": f"on {branch or 'a detached HEAD'}, not main"}
    present = [p for p in paths if (repo / p).exists()]
    if not present:
        return {"skipped": "no paths present"}
    if not _git(repo, "status", "--porcelain", "--", *present).stdout.strip():
        return {"skipped": "nothing changed"}
    add = _git(repo, "add", "-A", "--", *present)
    if add.returncode:
        return {"skipped": "git add failed: " + add.stderr.strip()[:200]}
    commit = _git(repo, "commit", "-q", "-m", message, "--", *present)
    if commit.returncode:
        return {"skipped": "git commit failed: " + (commit.stderr or commit.stdout).strip()[:200]}
    return {"commit": _git(repo, "rev-parse", "--short", "HEAD").stdout.strip()}


def push(repo: Path) -> dict:
    """Push main if it is ahead of its upstream. Never forced; a rejection is reported and retried next time."""
    ahead = _git(repo, "rev-list", "--count", "@{u}..HEAD")
    if ahead.returncode:
        return {"error": "no upstream: " + ahead.stderr.strip()[:200]}
    if ahead.stdout.strip() == "0":
        return {"pushed": False, "reason": "up to date"}
    r = _git(repo, "push", "-q", "origin", "main", timeout=300)
    return {"pushed": r.returncode == 0, **({"error": (r.stderr or r.stdout).strip()[:300]} if r.returncode else {})}


def rerank(root: Path = ROOT) -> dict:
    t0 = time.time()
    r = subprocess.run([sys.executable, str(root / "atlas-data" / "rank_problems.py")], cwd=root,
                       capture_output=True, text=True, timeout=900)
    return {"ok": r.returncode == 0, "secs": round(time.time() - t0, 1),
            **({"error": (r.stderr or r.stdout).strip()[-300:]} if r.returncode else {})}


def _load_state() -> dict:
    try:
        return json.loads(STATE.read_text())
    except (OSError, ValueError):
        return {}


def _save_state(st: dict) -> None:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_name(STATE.name + f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(st, indent=1))
    tmp.replace(STATE)


def maybe_refresh(root: Path = ROOT, now: float | None = None, force: bool = False, do_push: bool = True) -> dict:
    """One step of the self-maintaining Atlas. Cheap when nothing changed; never raises."""
    now = time.time() if now is None else now
    st = _load_state()
    out: dict = {"at": now_iso()}
    try:
        sig = inputs_signature(root)
        if force or (sig != st.get("sig") and now - st.get("reranked_at", 0) >= RERANK_EVERY):
            out["rerank"] = rerank(root)
            if out["rerank"]["ok"]:
                st.update(sig=inputs_signature(root), reranked_at=now)
        if force or now - st.get("committed_at", 0) >= COMMIT_EVERY:
            c = commit_paths(root, HARNESS_PATHS, "Atlas: automatic refresh (atlas_refresh.py)")
            out["harness_commit"] = c
            if do_push and ("commit" in c or c.get("skipped") == "nothing changed"):
                out["harness_push"] = push(root)
            st["committed_at"] = now
        if (force or now - st.get("deployed_at", 0) >= DEPLOY_EVERY) and (root / "erdos-atlas").is_dir():
            site = root / "erdos-atlas"
            c = commit_paths(site, SITE_PATHS, "Refresh baked ranking snapshot (automatic, atlas_refresh.py)")
            out["site_commit"] = c
            if do_push and ("commit" in c or c.get("skipped") == "nothing changed"):
                out["site_push"] = push(site)      # the site deploys from its repository
            st["deployed_at"] = now
    except Exception as e:                          # noqa: BLE001 - the publisher loop must keep publishing
        out["error"] = f"{type(e).__name__}: {str(e)[:200]}"
    st["last"] = out
    _save_state(st)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--no-push", action="store_true")
    a = ap.parse_args()
    out = maybe_refresh(force=a.force, do_push=not a.no_push)
    print(json.dumps(out, indent=1))
    return 1 if out.get("error") or not (out.get("rerank") or {}).get("ok", True) else 0


if __name__ == "__main__":
    sys.exit(main())
