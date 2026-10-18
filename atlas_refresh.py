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
  DEPLOY_EVERY seconds. That repository is the ChatGPT Sites source, and Sites deploys only from the ChatGPT app, so
  this keeps the source current but does not put it live.
- **Publish** the encrypted GitHub Pages site (`atlas_pages.py`): rebuild, encrypt and push when the snapshot, the run
  feed or the page changed, at most every PAGES_EVERY seconds, plus an hourly heartbeat. This is the deploy that puts
  the Atlas live.

Git safety: a repository is committed to only when it is on `main` with no merge, rebase, cherry-pick, revert or index
lock in progress. Only the listed paths are staged and committed (`git commit -- <paths>`), so anyone's other work in
the checkout is left alone. Nothing is ever force-pushed. The per-alias research-guidance files are never committed.

When origin moves: a session that pushes its branch straight to `origin main` leaves the main checkout's `main` behind,
and every later push is refused. On 2026-10-15 four commits sat unpushed for about 2.5 hours that way, until a session
merged by hand. A push refused as not a fast-forward now runs `reconcile`. It fetches, merges `origin/main` into local
`main` and pushes once more, but only when that is safe:
- nothing is in progress (as for a commit) and nothing is staged;
- every commit that origin lacks is automatic: the publisher's own or the resolution campaign's (`resolution.commit`),
  each confined to its own paths, or an earlier reconcile merge;
- the merge would not conflict, and it writes no uncommitted, untracked or ignored file and nothing under
  `.result-feed/`. A merge overwrites an ignored file without a word, and the Pages passphrase is one.
Otherwise the checkout is left alone. A push that does not get through stays on record under `push_stuck` in the state
file (since when, how many tries, why) until one does, with a line on stderr for each failed try.
"""
from __future__ import annotations
import argparse, datetime as dt, hashlib, json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STATE = ROOT / ".result-feed" / "atlas-refresh.json"
SITE = ROOT / "erdos-atlas"
RERANK_EVERY, COMMIT_EVERY, DEPLOY_EVERY, PAGES_EVERY = 300, 900, 1800, 600
HARNESS_PATHS = ["atlas-data/reviewed.json", "atlas-data/rankings.json", "atlas-data/rankings.csv",
                 "atlas-data/briefs", "atlas-data/predictions.jsonl"]
SITE_PATHS = ["app/data.json"]
COMMIT_MESSAGE = "Atlas: automatic refresh (atlas_refresh.py)"
SITE_COMMIT_MESSAGE = "Refresh baked ranking snapshot (automatic, atlas_refresh.py)"
MERGE_MESSAGE = "Atlas: merge origin/main into main (atlas_refresh.py)"
# The commits `reconcile` may merge origin/main around: each automatic writer's subject prefix and the only paths its
# commits touch. The resolution campaign commits its state from the main checkout (`resolution.commit`), and one of its
# commits was among the four stuck on 2026-10-15.
AUTOMATIC = [(COMMIT_MESSAGE, HARNESS_PATHS), ("resolution: #", ["resolution"])]
SITE_AUTOMATIC = [(SITE_COMMIT_MESSAGE, SITE_PATHS)]
UPSTREAM = "refs/remotes/origin/main"
BUSY = ("MERGE_HEAD", "rebase-merge", "rebase-apply", "index.lock", "CHERRY_PICK_HEAD", "REVERT_HEAD")
NEVER = ".result-feed/"        # holds the Pages passphrase: no merge may write under it


def now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _iso(t: float) -> str:
    return dt.datetime.fromtimestamp(t, dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


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


def _busy(repo: Path) -> str | None:
    """Why git must not be touched in `repo` now (a merge, rebase, cherry-pick or revert in progress, or a held index
    lock), or None."""
    return next((f"{b} present" for b in BUSY if (repo / ".git" / b).exists()), None)


def commit_paths(repo: Path, paths: list[str], message: str) -> dict:
    """Commit exactly `paths` (their working-tree state) on main. Returns {"commit": sha} or {"skipped": why}."""
    if not (repo / ".git").exists():
        return {"skipped": "not a git repository"}
    if (busy := _busy(repo)):
        return {"skipped": busy}
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


def _push_once(repo: Path) -> tuple[bool, str, bool]:
    """One `git push origin main`: (pushed, what went wrong, whether the remote refused it as not a fast-forward)."""
    r = _git(repo, "push", "--porcelain", "origin", "main", timeout=300)
    if r.returncode == 0:
        return True, "", False
    refused = [line.split("\t")[-1] for line in r.stdout.splitlines() if line.startswith("!\t")]
    if refused:
        return False, refused[0], refused[0].startswith("[rejected]")
    return False, (r.stderr or r.stdout).strip()[:300], False


def _within(path: str, paths: list[str]) -> bool:
    return any(path == p or path.startswith(p.rstrip("/") + "/") for p in paths)


def _local_commits(repo: Path, theirs: str) -> list[tuple[str, list[str], str, list[str]]] | None:
    """The commits on local main that origin's `theirs` lacks, as (sha, parents, subject, paths). A merge lists no
    paths."""
    r = _git(repo, "log", "--no-renames", "--name-only", "--format=%x00%H %P%x00%s", f"{theirs}..HEAD")
    if r.returncode:
        return None
    parts, commits = r.stdout.split("\0")[1:], []
    for head, body in zip(parts[0::2], parts[1::2]):
        sha, *parents = head.split()
        subject, *paths = body.split("\n")
        commits.append((sha, parents, subject, [p for p in paths if p]))
    return commits


def _automatic(repo: Path, commit: tuple, automatic: list, theirs: str) -> bool:
    """Whether `reconcile` may merge origin's `theirs` around this local commit. It must be an automatic writer's: its
    subject starts with the writer's prefix and it touches only the writer's paths (git quotes an unusual path, which
    then never matches). A merge must be an earlier reconcile whose other parents `theirs` already has."""
    sha, parents, subject, paths = commit
    if len(parents) > 1:
        return subject == MERGE_MESSAGE and all(
            _git(repo, "merge-base", "--is-ancestor", p, theirs).returncode == 0 for p in parents[1:])
    return bool(paths) and any(subject.startswith(prefix) and all(_within(p, allowed) for p in paths)
                               for prefix, allowed in automatic)


def _changed(repo: Path, theirs: str, *flags: str) -> list[str] | None:
    """The paths origin's `theirs` changed since it and local main parted: the only files a merge of it can write."""
    r = _git(repo, "diff", "--name-only", "--no-renames", "-z", *flags, f"HEAD...{theirs}")
    return None if r.returncode else [p for p in r.stdout.split("\0") if p]


def _dirty(repo: Path) -> set[str] | None:
    """Every path `git status` reports: modified, staged, deleted, unmerged or untracked (an untracked directory ends
    in "/"). Ignored files are not among them. --no-optional-locks keeps the status off the index lock."""
    r = _git(repo, "--no-optional-locks", "status", "--porcelain=v1", "-z")
    if r.returncode:
        return None
    fields, paths, i = r.stdout.split("\0"), set(), 0
    while i < len(fields):
        if len(fields[i]) > 3:
            paths.add(fields[i][3:])
            if ("R" in fields[i][:2] or "C" in fields[i][:2]) and i + 1 < len(fields):
                i += 1                                   # a rename or copy names its source next
                paths.add(fields[i])
        i += 1
    return paths


def reconcile(repo: Path, automatic: list = AUTOMATIC) -> dict:
    """After the remote refused a push because origin/main moved: fetch it, and merge it into local main when that is
    safe (the module docstring lists the conditions). Returns {"merged": sha, "behind": n, "ahead": m}, the commits
    each side lacked before the merge, or {"skipped": why} with the checkout untouched. Never rebases, resets or
    forces anything."""
    if (busy := _busy(repo)):
        return {"skipped": busy}
    branch = _git(repo, "symbolic-ref", "--short", "HEAD").stdout.strip()
    if branch != "main":
        return {"skipped": f"on {branch or 'a detached HEAD'}, not main"}
    fetch = _git(repo, "fetch", "-q", "origin", f"+refs/heads/main:{UPSTREAM}", timeout=300)
    if fetch.returncode:
        return {"skipped": "fetch failed: " + (fetch.stderr or fetch.stdout).strip()[:200]}
    # every check and the merge itself use this one commit, whatever a concurrent fetch does to the ref meanwhile
    theirs = _git(repo, "rev-parse", "--verify", "-q", f"{UPSTREAM}^{{commit}}").stdout.strip()
    counts = _git(repo, "rev-list", "--left-right", "--count", f"{theirs}...HEAD").stdout.split() if theirs else []
    if len(counts) != 2:
        return {"skipped": "could not compare main with origin/main"}
    behind, ahead = int(counts[0]), int(counts[1])
    if not behind:
        return {"skipped": "origin/main has nothing that local main lacks, so the push failed for another reason"}
    commits = _local_commits(repo, theirs)
    if commits is None or len(commits) != ahead:
        return {"skipped": "could not list the commits that origin lacks"}
    foreign = [f"{c[0][:7]} {c[2]}" for c in commits if not _automatic(repo, c, automatic, theirs)]
    if foreign:
        return {"skipped": f"{len(foreign)} commit(s) that origin lacks are not automatic: " + "; ".join(foreign[:3])}
    if _git(repo, "diff", "--cached", "--quiet").returncode:
        return {"skipped": "changes are staged in the index"}
    incoming, added, dirty = _changed(repo, theirs), _changed(repo, theirs, "--diff-filter=A"), _dirty(repo)
    if incoming is None or added is None or dirty is None:
        return {"skipped": "could not list what the merge would write"}
    if (secret := [p for p in incoming if p.startswith(NEVER)]):
        return {"skipped": "the merge would write under .result-feed/: " + ", ".join(secret[:3])}
    touched = [p for p in incoming if p in dirty or any(d.endswith("/") and p.startswith(d) for d in dirty)]
    if touched:
        return {"skipped": "the merge would touch uncommitted work: " + ", ".join(touched[:5])}
    # git merge overwrites an ignored file in its way without a word, so a file it would create must not exist yet
    hidden = [p for p in added if os.path.lexists(repo / p) and _git(repo, "cat-file", "-e", f"HEAD:{p}").returncode]
    if hidden:
        return {"skipped": "the merge would overwrite untracked or ignored files: " + ", ".join(hidden[:5])}
    trial = _git(repo, "merge-tree", "--write-tree", "--name-only", "--no-messages", "HEAD", theirs)
    if trial.returncode == 1:
        return {"skipped": "the merge would conflict in: " + ", ".join(trial.stdout.splitlines()[1:6])}
    if trial.returncode:
        return {"skipped": "could not try the merge: " + (trial.stderr or trial.stdout).strip()[:200]}
    message = (f"{MERGE_MESSAGE}\n\nThe remote refused the publisher's push: origin/main had {behind} commit(s) that "
               f"local main lacked, and local main had {ahead} automatic commit(s) that origin lacked.")
    merge = _git(repo, "merge", "--ff", "--no-edit", "-q", "-m", message, theirs, timeout=300)
    if merge.returncode:
        merging = repo / ".git" / "MERGE_HEAD"
        if merging.exists() and merging.read_text().strip() == theirs:    # this merge, not one someone began meanwhile
            _git(repo, "merge", "--abort")
        return {"skipped": "git merge failed: " + (merge.stderr or merge.stdout).strip()[:200]}
    return {"merged": _git(repo, "rev-parse", "--short", "HEAD").stdout.strip(), "behind": behind, "ahead": ahead}


def push(repo: Path, automatic: list = AUTOMATIC) -> dict:
    """Push main if it is ahead of its upstream. Never forced. When the remote refuses it because origin/main moved,
    `reconcile` merges origin/main in if that is safe and main is pushed once more. Otherwise the refusal comes back
    with the reason (`not_reconciled`), for `maybe_refresh` to keep on record, and the next cycle tries again."""
    ahead = _git(repo, "rev-list", "--count", "@{u}..HEAD")
    if ahead.returncode:
        return {"error": "no upstream: " + ahead.stderr.strip()[:200]}
    if ahead.stdout.strip() == "0":
        return {"pushed": False, "reason": "up to date"}
    pushed, error, moved = _push_once(repo)
    if pushed or not moved:
        return {"pushed": pushed, **({"error": error} if error else {})}
    rec = reconcile(repo, automatic)
    if "merged" not in rec:
        return {"pushed": False, "error": error, "not_reconciled": rec["skipped"]}
    if not rec["ahead"]:                    # origin already had every local commit, so the merge was a fast-forward
        return {"pushed": False, "reason": "up to date", "reconciled": rec}
    pushed, error, _ = _push_once(repo)
    return {"pushed": pushed, "reconciled": rec, **({"error": error} if error else {})}


def _through(res: dict) -> bool:
    return bool(res.get("pushed")) or res.get("reason") == "up to date"


def _note_push(st: dict, key: str, res: dict, now: float) -> None:
    """Keep a push that does not get through on record until one does: `push_stuck[key]` in the state file (since when,
    how many tries, why), and a line on stderr for each failed try, which the LaunchAgent writes to
    publisher-error.log. A failure used to live only in `last`, which the next 30-second cycle overwrites."""
    stuck = st.get("push_stuck") or {}
    if _through(res):
        stuck.pop(key, None)
    else:
        prev = stuck.get(key) or {}
        why = "; ".join(x for x in (res.get("error"), res.get("not_reconciled")) if x) or "unknown"
        entry = stuck[key] = {"since": prev.get("since", _iso(now)), "last_try": _iso(now),
                              "tries": prev.get("tries", 0) + 1, "why": why}
        print(f"atlas_refresh: the {key} push has not got through since {entry['since']} ({entry['tries']} tries): "
              f"{why}", file=sys.stderr, flush=True)
    if stuck:
        st["push_stuck"] = stuck
    else:
        st.pop("push_stuck", None)


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
            c = commit_paths(root, HARNESS_PATHS, COMMIT_MESSAGE)
            out["harness_commit"] = c
            if do_push and ("commit" in c or c.get("skipped") == "nothing changed"):
                out["harness_push"] = push(root)
                _note_push(st, "harness", out["harness_push"], now)
            st["committed_at"] = now
        if (force or now - st.get("deployed_at", 0) >= DEPLOY_EVERY) and (root / "erdos-atlas").is_dir():
            site = root / "erdos-atlas"
            c = commit_paths(site, SITE_PATHS, SITE_COMMIT_MESSAGE)
            out["site_commit"] = c
            if do_push and ("commit" in c or c.get("skipped") == "nothing changed"):
                out["site_push"] = push(site, SITE_AUTOMATIC)      # the site deploys from its repository
                _note_push(st, "site", out["site_push"], now)
            st["deployed_at"] = now
        if force or now - st.get("pages_at", 0) >= PAGES_EVERY:
            import atlas_pages
            if atlas_pages.configured(root):
                out["pages"] = atlas_pages.deploy(root, now=now, force=force, do_push=do_push)
            st["pages_at"] = now
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
    stuck = any(k in out and not _through(out[k]) for k in ("harness_push", "site_push"))
    return 1 if out.get("error") or not (out.get("rerank") or {}).get("ok", True) or stuck else 0


if __name__ == "__main__":
    sys.exit(main())
