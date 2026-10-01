#!/usr/bin/env python3
"""Publish the Erdős Atlas as an encrypted static site on GitHub Pages, and keep it current.

    python3 atlas_pages.py setup --repo nkudeba/erdos-atlas-site   # once: deploy checkout, passphrase, salt
    python3 atlas_pages.py deploy [--force] [--no-push]             # what atlas_refresh.py runs every 10 minutes
    python3 atlas_pages.py status

Why it exists (2026-10-01). ChatGPT Sites has no CLI, API or git integration for deploys; only the ChatGPT app can
deploy. So the daemon could commit the site's baked snapshot but never put it live. GitHub Pages is free and
pushable with the existing `gh` login, but a free-plan Pages site is public. So everything with content is
encrypted, and the operator chose this trade-off:
- the page's own code, the ranking snapshot and the live run feed are each IV || AES-256-GCM(gzip(content));
- the key is PBKDF2-SHA256 of a passphrase (600,000 iterations, a random 16-byte salt);
- `erdos-atlas/static/unlock.html` is the only page in plaintext, and it holds no content;
- plaintext otherwise: `meta.json` (salt, iteration count, a check value, file names), the KaTeX fonts, robots.txt.

Local files, all under `.result-feed/`, which is never committed:
- `pages/`: a deploy-only git checkout of the Pages repo;
- `pages-passphrase`: generated once, mode 600, never printed. Read it there to open the site;
- `pages-state.json`: salt, content hash, last deploy;
- `pages-feed.json`: the last plaintext feed, for debugging.

Each deploy is ONE parentless commit, force-pushed to the deploy repo's `main`. That branch holds only the current
build: re-encrypting changes every byte, and a normal history would grow by the size of the site on every deploy.
That is the only force-push anywhere in the Atlas tooling, and it targets only this deploy-only repo.

The feed mirrors `/api/results` on Sites (`erdos-atlas/app/api/results/route.ts`): every run's allowlisted status
summary (`result_feed.summarize`, status only for benchmark runs), the latest five per problem plus each problem's
strongest evidence, per-problem run counts, and the reviewed problems' score revisions (`result_feed.ranking_rows`).
No model calls.
"""
from __future__ import annotations
import argparse, base64, datetime as dt, fcntl, hashlib, json, os, secrets, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SITE = ROOT / "erdos-atlas"
LOCAL = ROOT / ".result-feed"
DEPLOY = LOCAL / "pages"
PASSFILE = LOCAL / "pages-passphrase"
STATE = LOCAL / "pages-state.json"
FEED = LOCAL / "pages-feed.json"
LOCK = LOCAL / "pages.lock"
ITERATIONS = 600_000
HEARTBEAT = 3600          # redeploy unchanged content hourly, so the page can tell a live publisher from a dead one
ALPHABET = "abcdefghjkmnpqrstuvwxyz23456789"   # no 0/o, 1/l/i: the passphrase is typed on phones too
BUILD_INPUTS = ["app/atlas.tsx", "app/globals.css", "app/katex.css", "vite.static.config.ts", "package-lock.json",
                "static", "components", "lib"]


def now_iso() -> str:
    t = dt.datetime.now(dt.timezone.utc)
    return t.strftime("%Y-%m-%dT%H:%M:%S.") + f"{t.microsecond // 1000:03d}Z"


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _node() -> str | None:
    """The LaunchAgent's PATH is /usr/bin:/bin, so look where Homebrew and the installer put node."""
    found = shutil.which("node")
    for cand in ([found] if found else []) + ["/opt/homebrew/bin/node", "/usr/local/bin/node"]:
        if cand and Path(cand).exists():
            return cand
    return None


def _git(*args, cwd: Path | None = None, timeout: int = 120) -> subprocess.CompletedProcess:
    cwd = DEPLOY if cwd is None else cwd            # resolved per call, as PASSFILE is
    return subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, text=True, timeout=timeout)


def load_state() -> dict:
    try:
        return json.loads(STATE.read_text())
    except (OSError, ValueError):
        return {}


def save_state(st: dict) -> None:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_name(STATE.name + f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(st, indent=1))
    tmp.replace(STATE)


def ensure_passphrase(path: Path | None = None) -> bool:
    """Create the passphrase once: 30 characters from a 31-letter alphabet, about 148 bits. True if created."""
    path = PASSFILE if path is None else path       # resolved per call, so a test's patch of PASSFILE holds
    if path.exists():
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    groups = ["".join(secrets.choice(ALPHABET) for _ in range(5)) for _ in range(6)]
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w") as f:
        f.write("-".join(groups) + "\n")
    return True


def ensure_salt(st: dict) -> dict:
    if not st.get("salt"):
        st["salt"] = base64.b64encode(secrets.token_bytes(16)).decode()
        st["iterations"] = ITERATIONS
    return st


def aggregate(rows: list[dict]) -> tuple[list[dict], list[dict]]:
    """The Sites endpoint's selection: per problem, the five most recent runs plus the strongest evidence."""
    by: dict[int, list[dict]] = {}
    for r in rows:
        by.setdefault(r["problem"], []).append(r)
    keep, counts = [], []
    for pid in sorted(by):
        runs = by[pid]
        # newest first, ties broken by id ascending, as `ORDER BY updated_at DESC, id` does (both sorts are stable)
        recent = sorted(sorted(runs, key=lambda r: r["id"]), key=lambda r: r["updatedAt"], reverse=True)
        best = max(runs, key=lambda r: (r["claimEligible"], r["mechanical"], r["faithful"], r["partial"], r["updatedAt"]))
        chosen = {r["id"]: r for r in recent[:5]}
        chosen.setdefault(best["id"], best)
        keep += list(chosen.values())
        counts.append({"problem": pid, "count": len(runs)})
    return keep, counts


def run_rows(root: Path = ROOT) -> list[dict]:
    """Every run's publishable summary, with the same filters as `result_feed.sync`."""
    import atlas_ids, result_feed
    aliases = atlas_ids.benchmark_aliases(root)
    rows = []
    for state in (root / "runs").rglob("state.json"):
        run = state.parent
        if state.is_symlink() or "current" in run.parts or ".cache" in run.parts:
            continue
        if run.relative_to(root / "runs").parts[0].startswith("replay-"):
            continue
        try:
            row = result_feed.summarize(run, root, aliases)
        except (ValueError, TypeError, AttributeError, OSError):
            continue
        if row:
            rows.append(row)
    return rows


def static_feed(root: Path = ROOT, rows: list[dict] | None = None) -> dict:
    import result_feed
    runs, counts = aggregate(run_rows(root) if rows is None else rows)
    stamp = now_iso()
    return {"runs": runs, "counts": counts, "rankings": result_feed.ranking_rows(root),
            "publisherSeenAt": stamp, "receivedAt": stamp}


def feed_content_hash(feed: dict) -> str:
    """What the feed says, without the times it was assembled at (ranking revisions carry a timestamp prefix)."""
    rankings = [{k: v for k, v in r.items() if k not in ("revision", "updatedAt")} for r in feed["rankings"]]
    return _sha(json.dumps({"runs": feed["runs"], "counts": feed["counts"], "rankings": rankings}, sort_keys=True).encode())


def build_signature(site: Path | None = None) -> str:
    site = SITE if site is None else site
    h = hashlib.sha256()
    for rel in BUILD_INPUTS:
        p = site / rel
        files = sorted(x for x in p.rglob("*") if x.is_file()) if p.is_dir() else ([p] if p.exists() else [])
        for f in files:
            h.update(str(f.relative_to(site)).encode())
            h.update(f.read_bytes())
    return h.hexdigest()


def build_app(st: dict, site: Path | None = None) -> dict:
    site = SITE if site is None else site
    sig = build_signature(site)
    if st.get("app_sig") == sig and (site / "dist-static" / "app.js").exists() and (site / "dist-static" / "app.css").exists():
        return {"built": False}
    node = _node()
    if not node:
        return {"error": "node not found"}
    r = subprocess.run([node, str(site / "node_modules" / "vite" / "bin" / "vite.js"), "build", "--config",
                        "vite.static.config.ts"], cwd=site, capture_output=True, text=True, timeout=600)
    if r.returncode:
        return {"error": "static build failed: " + (r.stderr or r.stdout).strip()[-300:]}
    st["app_sig"] = sig
    return {"built": True}


def configured(root: Path = ROOT) -> bool:
    deploy = root / ".result-feed" / "pages"
    return (deploy / ".git").exists() and bool(_git("remote", "get-url", "origin", cwd=deploy).stdout.strip())


def setup(repo: str) -> dict:
    """One-time: the deploy checkout (identity = the GitHub noreply address), the passphrase and the salt."""
    DEPLOY.mkdir(parents=True, exist_ok=True)
    if not (DEPLOY / ".git").exists():
        _git("init", "-q", "-b", "main")
    url = f"https://github.com/{repo}.git"
    if _git("remote", "get-url", "origin").returncode:
        _git("remote", "add", "origin", url)
    else:
        _git("remote", "set-url", "origin", url)
    uid = subprocess.run(["gh", "api", "user", "--jq", ".id"], capture_output=True, text=True, timeout=60).stdout.strip()
    login = repo.split("/")[0]
    _git("config", "user.name", "Atlas deploy")
    _git("config", "user.email", f"{uid}+{login}@users.noreply.github.com" if uid.isdigit() else f"{login}@users.noreply.github.com")
    created = ensure_passphrase()
    st = ensure_salt(load_state())
    st["repo"] = repo
    save_state(st)
    return {"deploy_dir": str(DEPLOY), "remote": url, "passphrase_created": created, "passphrase_file": str(PASSFILE)}


def deploy(root: Path = ROOT, now: float | None = None, force: bool = False, do_push: bool = True) -> dict:
    """Build, encrypt and push when anything changed, or hourly as a heartbeat. Never raises. One deploy at a time:
    the daemon and a manual `deploy` share the checkout, so a second caller skips instead of waiting."""
    now = time.time() if now is None else now
    try:
        if not configured(root):
            return {"skipped": "not configured (python3 atlas_pages.py setup --repo OWNER/NAME)"}
        LOCK.parent.mkdir(parents=True, exist_ok=True)
        with LOCK.open("w") as held:
            try:
                fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return {"skipped": "another deploy is running"}
            return _deploy_locked(root, now, force, do_push)
    except Exception as e:   # noqa: BLE001 - the publisher loop must keep publishing
        return {"error": f"{type(e).__name__}: {str(e)[:200]}"}


def _deploy_locked(root: Path, now: float, force: bool, do_push: bool) -> dict:
    ensure_passphrase()
    st = ensure_salt(load_state())
    out = {"build": build_app(st)}
    if out["build"].get("error"):
        save_state(st)
        return out
    feed = static_feed(root)
    data = (SITE / "app" / "data.json").read_bytes()
    content = _sha("|".join([_sha(data), feed_content_hash(feed), st.get("app_sig", ""),
                             _sha((SITE / "static" / "unlock.html").read_bytes()),
                             _sha((SITE / "scripts" / "publish-static.mjs").read_bytes())]).encode())
    if not force and content == st.get("content") and now - st.get("deployed_at", 0) < HEARTBEAT:
        save_state(st)
        return {**out, "skipped": "unchanged"}
    FEED.write_text(json.dumps(feed))
    node = _node()
    r = subprocess.run([node, str(SITE / "scripts" / "publish-static.mjs"), "--out", str(DEPLOY),
                        "--passphrase-file", str(PASSFILE), "--salt", st["salt"], "--iterations", str(st["iterations"]),
                        "--data", str(SITE / "app" / "data.json"), "--feed", str(FEED),
                        "--app-dir", str(SITE / "dist-static"), "--fonts", str(SITE / "public" / "fonts"),
                        "--unlock", str(SITE / "static" / "unlock.html"), "--deployed-at", feed["receivedAt"]],
                       capture_output=True, text=True, timeout=300)
    if r.returncode:
        return {**out, "error": "encrypt failed: " + (r.stderr or r.stdout).strip()[-300:]}
    out["encrypt"] = json.loads(r.stdout.strip().splitlines()[-1])
    _git("add", "-A")
    tree = _git("write-tree").stdout.strip()
    commit = _git("commit-tree", tree, "-m", f"Deploy {feed['receivedAt']}").stdout.strip()
    if not commit:
        return {**out, "error": "commit failed"}
    _git("update-ref", "refs/heads/main", commit)
    _git("symbolic-ref", "HEAD", "refs/heads/main")
    out["commit"] = commit[:12]
    if do_push:
        p = _git("push", "-q", "-f", "origin", "main", timeout=300)
        out["pushed"] = p.returncode == 0
        if p.returncode:
            out["push_error"] = (p.stderr or p.stdout).strip()[:300]
            save_state(st)
            return out
    st.update(content=content, deployed_at=now, commit=commit[:12], at=feed["receivedAt"])
    save_state(st)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("setup")
    s.add_argument("--repo", required=True, help="OWNER/NAME of the public, deploy-only Pages repository")
    d = sub.add_parser("deploy")
    d.add_argument("--force", action="store_true")
    d.add_argument("--no-push", action="store_true")
    sub.add_parser("status")
    a = ap.parse_args()
    if a.cmd == "setup":
        print(json.dumps(setup(a.repo), indent=1))
        return 0
    if a.cmd == "deploy":
        out = deploy(force=a.force, do_push=not a.no_push)
        print(json.dumps(out, indent=1))
        return 1 if out.get("error") or out.get("push_error") else 0
    st = load_state()
    print(json.dumps({k: st.get(k) for k in ("repo", "commit", "at", "iterations")} | {"configured": configured()}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
