"""The encrypted GitHub Pages site (atlas_pages.py). The feed selects what /api/results selects. The passphrase is
created once, mode 600, and never printed. A deploy happens only on a change or the hourly heartbeat, and each one is
a single parentless commit. The pushed files decrypt in WebCrypto exactly as the browser does it. Git runs against a
throwaway bare remote. No network, no model calls."""
import fcntl, io, json, os, re, shutil, stat, subprocess, sys, tempfile, unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import atlas_pages as P
import atlas_refresh as R

NODE = P._node()


def row(pid, n, minute, **kw):
    return {"id": f"{pid:04d}{n:060d}", "problem": pid, "revision": str(n).zfill(20),
            "updatedAt": f"2026-10-01T00:{minute:02d}:00.000Z", "outcome": "running", "phase": "", "direction": "pos",
            "stage": "no_candidate", "mechanical": False, "faithful": False, "claimEligible": False, "partial": False,
            "artifact": None, **kw}


class Feed(unittest.TestCase):
    def test_latest_five_plus_strongest_evidence_and_counts(self):
        rows = [row(7, i, i, mechanical=(i == 0), stage="mechanically_verified" if i == 0 else "no_candidate")
                for i in range(7)] + [row(9, i, i) for i in range(2)]
        runs, counts = P.aggregate(rows)
        kept7 = sorted(r["updatedAt"][14:16] for r in runs if r["problem"] == 7)
        self.assertEqual(kept7, ["00", "02", "03", "04", "05", "06"])   # five newest, plus the oldest: it verified
        self.assertEqual(len([r for r in runs if r["problem"] == 9]), 2)
        self.assertEqual(counts, [{"problem": 7, "count": 7}, {"problem": 9, "count": 2}])

    def test_assembly_times_alone_never_count_as_a_change(self):
        feed = {"runs": [row(7, 1, 1)], "counts": [{"problem": 7, "count": 1}], "publisherSeenAt": "a", "receivedAt": "a",
                "rankings": [{"problem": 7, "revision": "1".zfill(20), "updatedAt": "t1", "score": 50, "rationale": [],
                              "requirements": [], "partialScore": None, "brief": None}]}
        later = json.loads(json.dumps(feed))
        later.update(publisherSeenAt="b", receivedAt="b")
        later["rankings"][0].update(revision="2".zfill(20), updatedAt="t2")
        self.assertEqual(P.feed_content_hash(feed), P.feed_content_hash(later))
        later["runs"][0]["outcome"] = "proved"
        self.assertNotEqual(P.feed_content_hash(feed), P.feed_content_hash(later))


class Passphrase(unittest.TestCase):
    def test_created_once_private_and_never_printed(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "pages-passphrase"
            buf = io.StringIO()
            with redirect_stdout(buf):
                self.assertTrue(P.ensure_passphrase(path))
                first = path.read_text()
                self.assertFalse(P.ensure_passphrase(path))
            self.assertEqual(buf.getvalue(), "")
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o600)
            self.assertRegex(first.strip(), r"^[a-z2-9]{5}(-[a-z2-9]{5}){5}$")
            self.assertTrue(set(first.strip().replace("-", "")) <= set(P.ALPHABET))
            self.assertEqual(path.read_text(), first)


ROUNDTRIP = r"""
import { readFileSync } from 'node:fs';
const dir = process.argv[2], pass = readFileSync(process.argv[3], 'utf8').trim();
const meta = JSON.parse(readFileSync(dir + '/meta.json', 'utf8'));
const b64 = (s) => Uint8Array.from(atob(s), (c) => c.charCodeAt(0));
const base = await crypto.subtle.importKey('raw', new TextEncoder().encode(pass), 'PBKDF2', false, ['deriveKey']);
const key = await crypto.subtle.deriveKey({ name: 'PBKDF2', hash: 'SHA-256', salt: b64(meta.kdf.salt),
  iterations: meta.kdf.iterations }, base, { name: 'AES-GCM', length: 256 }, true, ['decrypt']);
async function open(bytes) {
  const plain = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: bytes.slice(0, 12) }, key, bytes.slice(12));
  const stream = new Blob([plain]).stream().pipeThrough(new DecompressionStream('gzip'));
  return new TextDecoder().decode(await new Response(stream).arrayBuffer());
}
const file = (name) => new Uint8Array(readFileSync(dir + '/' + name.split('?')[0]));
const app = JSON.parse(await open(file(meta.app)));
console.log(JSON.stringify({ check: await open(b64(meta.check)), js: app.js, css: app.css,
  data: JSON.parse(await open(file(meta.data))), live: JSON.parse(await open(file(meta.live))) }));
"""


@unittest.skipUnless(NODE and shutil.which("git"), "needs node and git")
class Deploy(unittest.TestCase):
    """deploy() end to end: the real publish script, a real deploy checkout, a local bare remote."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = self.root = Path(self.tmp.name)
        site = t / "erdos-atlas"
        for rel in ("app", "static", "scripts", "dist-static", "public/fonts"):
            (site / rel).mkdir(parents=True)
        (site / "app" / "data.json").write_text(json.dumps({"meta": {"total": 1}, "problems": [{"id": 1, "statement": "SECRET-STATEMENT"}]}))
        shutil.copy(ROOT / "erdos-atlas" / "static" / "unlock.html", site / "static" / "unlock.html")
        shutil.copy(ROOT / "erdos-atlas" / "scripts" / "publish-static.mjs", site / "scripts" / "publish-static.mjs")
        (site / "dist-static" / "app.js").write_text("console.log('atlas')")
        (site / "dist-static" / "app.css").write_text(".x{src:url(/fonts/A.woff2)}")
        (site / "public" / "fonts" / "A.woff2").write_bytes(b"font")
        local = t / ".result-feed"
        self.remote = t / "remote.git"
        env = {**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null"}
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(self.remote)], check=True, env=env)
        deploy = local / "pages"
        deploy.mkdir(parents=True)
        for args in (["init", "-q", "-b", "main"], ["remote", "add", "origin", str(self.remote)],
                     ["config", "user.name", "t"], ["config", "user.email", "t@t"]):
            subprocess.run(["git", "-C", str(deploy), *args], check=True, env=env)
        self.feed_runs = [row(7, 1, 1)]
        consts = dict(SITE=site, LOCAL=local, DEPLOY=deploy, PASSFILE=local / "pages-passphrase",
                      STATE=local / "pages-state.json", FEED=local / "pages-feed.json", LOCK=local / "pages.lock")
        self.patches = [patch.object(P, k, v) for k, v in consts.items()]
        self.patches += [patch.object(P, "build_app", lambda st: (st.setdefault("app_sig", "test"), {"built": False})[1]),
                         patch.object(P, "static_feed", lambda root: {"runs": self.feed_runs, "counts": [], "rankings": [],
                                                                     "publisherSeenAt": P.now_iso(), "receivedAt": P.now_iso()})]
        for p in self.patches:
            p.start()
        self.local, self.deploy_dir = local, deploy

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def remote_git(self, *a):
        return subprocess.run(["git", "--git-dir", str(self.remote), *a], capture_output=True, text=True).stdout.strip()

    def test_change_or_heartbeat_only_one_parentless_commit_and_it_decrypts(self):
        first = P.deploy(self.root, now=1000.0)
        self.assertTrue(first.get("pushed"), first)
        self.assertEqual(self.remote_git("rev-list", "--count", "main"), "1")
        self.assertEqual(self.remote_git("log", "-1", "--format=%P", "main"), "")          # no parent
        files = set(self.remote_git("ls-tree", "-r", "--name-only", "main").split())
        self.assertEqual(files, {".nojekyll", "app.enc", "data.enc", "fonts/A.woff2", "index.html", "live.enc",
                                 "meta.json", "robots.txt"})
        for name in ("app.enc", "data.enc", "live.enc"):                                  # ciphertext only
            self.assertNotIn(b"SECRET-STATEMENT", (self.deploy_dir / name).read_bytes())
        self.assertEqual(stat.S_IMODE((self.local / "pages-passphrase").stat().st_mode), 0o600)

        self.assertEqual(P.deploy(self.root, now=1100.0).get("skipped"), "unchanged")
        self.feed_runs = [row(7, 1, 1, outcome="proved")]
        changed = P.deploy(self.root, now=1200.0)
        self.assertTrue(changed.get("pushed"), changed)
        self.assertEqual(self.remote_git("rev-list", "--count", "main"), "1")            # history never grows
        self.assertEqual(P.deploy(self.root, now=1300.0).get("skipped"), "unchanged")
        beat = P.deploy(self.root, now=1200.0 + P.HEARTBEAT)
        self.assertTrue(beat.get("pushed"), beat)

        script = self.root / "roundtrip.mjs"
        script.write_text(ROUNDTRIP)
        r = subprocess.run([NODE, str(script), str(self.deploy_dir), str(self.local / "pages-passphrase")],
                           capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        out = json.loads(r.stdout)
        self.assertEqual(out["check"], "erdos-atlas")
        self.assertEqual(out["js"], "console.log('atlas')")
        self.assertIn("url(fonts/A.woff2)", out["css"])                                   # relative under a Pages path
        self.assertEqual(out["data"]["problems"][0]["statement"], "SECRET-STATEMENT")
        self.assertEqual(out["live"]["runs"][0]["outcome"], "proved")
        meta = json.loads((self.deploy_dir / "meta.json").read_text())
        self.assertEqual(meta["kdf"]["iterations"], P.ITERATIONS)

    def test_a_second_deploy_skips_while_one_holds_the_lock(self):
        with (self.local / "pages.lock").open("w") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            self.assertEqual(P.deploy(self.root, now=1000.0), {"skipped": "another deploy is running"})

    def test_unconfigured_is_a_skip_not_an_error(self):
        shutil.rmtree(self.deploy_dir / ".git")
        self.assertIn("not configured", P.deploy(self.root, now=1000.0)["skipped"])


class RefreshTimer(unittest.TestCase):
    """maybe_refresh publishes the Pages site at most every PAGES_EVERY seconds, and only once it is configured."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.calls = []
        self.patches = [patch.object(R, "STATE", self.root / "atlas-refresh.json"),
                        patch.object(R, "inputs_signature", return_value="s"),
                        patch.object(R, "rerank", lambda root: {"ok": True}),
                        patch.object(R, "commit_paths", lambda *a: {"skipped": "nothing changed"}),
                        patch.object(R, "push", lambda repo: {"pushed": False}),
                        patch.object(P, "configured", lambda root: True),
                        patch.object(P, "deploy", lambda root, now, force, do_push: self.calls.append(now) or {"pushed": True})]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def test_pages_deploy_runs_on_its_own_timer(self):
        R.maybe_refresh(self.root, now=10_000)
        R.maybe_refresh(self.root, now=10_060)
        R.maybe_refresh(self.root, now=10_000 + R.PAGES_EVERY)
        self.assertEqual(self.calls, [10_000, 10_000 + R.PAGES_EVERY])

    def test_not_configured_means_no_deploy(self):
        with patch.object(P, "configured", lambda root: False):
            R.maybe_refresh(self.root, now=10_000)
        self.assertEqual(self.calls, [])


if __name__ == "__main__":
    unittest.main()
