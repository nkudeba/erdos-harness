"""The Atlas survives concurrent recorders.

`record_finding.py` mutated `atlas-data/reviewed.json` with a bare read-modify-write. Two agents
recording findings for DIFFERENT problems at the same time each read the same dict, each added their
own key, and whichever wrote second silently erased the other's entry -- both printing success. The
same `write_text` call opens with O_TRUNC, so an interrupted write left the Atlas's memory of every
assessed problem unparseable, which `load()` then silently reads as `{}`.

This matters because the project's own instructions make `reviewed.json` the thing that decides which
problem is attacked next, and because the harness deliberately runs work concurrently (`--open`
attacks both directions at once). A dropped finding is precisely the failure the Atlas exists to stop.
"""
import json, os, subprocess, sys, tempfile, unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "atlas-data"))
from atomic import atomic_write, atomic_write_json, locked  # noqa: E402


class AtomicWrite(unittest.TestCase):
    def test_replaces_whole_file(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            atomic_write_json(p, {"a": 1}, indent=2)
            atomic_write_json(p, {"b": 2}, indent=2)
            self.assertEqual(json.loads(p.read_text()), {"b": 2})

    def test_failed_write_leaves_the_old_file_intact_and_no_debris(self):
        """A crash mid-write must not truncate the target -- the old bytes stay readable."""
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            atomic_write(p, '{"keep": true}\n')

            import atomic as A
            real_fsync = A.os.fsync
            A.os.fsync = lambda fd: (_ for _ in ()).throw(OSError(28, "No space left on device"))
            try:
                with self.assertRaises(OSError):
                    atomic_write(p, '{"never": "written"}\n')
            finally:
                A.os.fsync = real_fsync
            self.assertEqual(json.loads(p.read_text()), {"keep": True})
            self.assertEqual([f for f in os.listdir(d) if f.endswith(".tmp")], [],
                             "a failed atomic_write left a temp file behind")

    def test_lock_is_not_held_on_the_replaced_inode(self):
        """The lock lives on a sibling file, so os.replace cannot drop it mid-critical-section."""
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.json"
            atomic_write_json(p, {})
            with locked(p):
                atomic_write_json(p, {"v": 1})
            self.assertTrue((Path(d) / ".x.json.lock").exists())


class ConcurrentRecorders(unittest.TestCase):
    """N agents recording findings for N different problems must yield N entries, not 1."""

    def _record(self, reviewed: Path, pid: int) -> None:
        with locked(reviewed):
            data = json.loads(reviewed.read_text())
            data[str(pid)] = {"score": pid, "rationale": [f"finding {pid}"]}
            # a real recorder does non-trivial work between the read and the write; without a lock
            # this window is exactly where the lost update happens.
            json.dumps(data)
            atomic_write_json(reviewed, dict(sorted(data.items(), key=lambda kv: int(kv[0]))), indent=2)

    def test_no_lost_updates(self):
        with tempfile.TemporaryDirectory() as d:
            reviewed = Path(d) / "reviewed.json"
            atomic_write_json(reviewed, {})
            pids = list(range(100, 140))
            with ThreadPoolExecutor(max_workers=16) as ex:
                list(ex.map(lambda p: self._record(reviewed, p), pids))
            got = json.loads(reviewed.read_text())
            self.assertEqual(sorted(int(k) for k in got), pids,
                             "a concurrent recorder's finding was silently dropped")

    def test_file_is_always_parseable_to_a_concurrent_reader(self):
        """A reader racing a writer never observes a truncated Atlas."""
        with tempfile.TemporaryDirectory() as d:
            reviewed = Path(d) / "reviewed.json"
            atomic_write_json(reviewed, {"1": {"score": 1}})
            bad = []

            def writer():
                for i in range(200):
                    atomic_write_json(reviewed, {str(j): {"score": j, "pad": "x" * 500}
                                                 for j in range(i)}, indent=2)

            def reader():
                for _ in range(400):
                    try:
                        json.loads(reviewed.read_text())
                    except ValueError as e:
                        bad.append(str(e))
            with ThreadPoolExecutor(max_workers=4) as ex:
                list(ex.map(lambda f: f(), [writer, reader, reader, reader]))
            self.assertEqual(bad, [], "a reader saw a partially written reviewed.json")


class RecordFindingUsesThem(unittest.TestCase):
    """The real script must actually route its writes through the safe helpers."""

    def test_no_bare_write_text_on_shared_atlas_files(self):
        src = (ROOT / "atlas-data" / "record_finding.py").read_text()
        self.assertIn("from atomic import", src)
        self.assertIn("with locked(REVIEWED)", src)
        self.assertNotIn("REVIEWED.write_text", src)
        self.assertNotIn('pf.write_text', src)

    def test_rank_problems_writes_atomically(self):
        src = (ROOT / "atlas-data" / "rank_problems.py").read_text()
        self.assertIn("from atomic import atomic_write", src)
        for f in ("rankings.json", "data.json", "rankings.csv"):
            self.assertNotIn(f"'{f}').write_text", src)

    def test_rerank_subprocess_runs_outside_the_lock(self):
        """Holding the exclusive lock across the ranker would serialise every recorder for no benefit."""
        src = (ROOT / "atlas-data" / "record_finding.py").read_text()
        body = src[src.index("def main()"):src.index("def _record(")]
        self.assertIn("with locked(REVIEWED):", body)
        lock_line = body.index("with locked(REVIEWED):")
        self.assertGreater(body.index("rank_problems.py"), lock_line)
        self.assertNotIn("        rank_problems.py", body.split("with locked(REVIEWED):")[1].split("\n")[1])


if __name__ == "__main__":
    unittest.main()
