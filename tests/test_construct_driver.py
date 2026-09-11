"""Construction-search driver: random search + mutation over a toy generator program, archive output (no model, no Lean)."""
import json, subprocess, sys, tempfile, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

TOY = '''
import random
PARAM_SPACE = {"N": [12, 16]}
def ok(A):
    s = set()
    for i in range(len(A)):
        for j in range(i, len(A)):
            if A[i] + A[j] in s: return False
            s.add(A[i] + A[j])
    return True
def generate(params, rng):
    A = []
    for x in range(1, params["N"] + 1):
        if ok(A + [x]): A.append(x)
    return A
def valid(A): return ok(A)
def score(A): return len(A)
def mutate(A, rng):
    B = list(A); x = rng.randint(1, 20)
    if x not in B and ok(B + [x]): B.append(x)
    return sorted(B)
def describe(A): return "size %d" % len(A)
def lean_certificate(A): return "theorem construct_cert : True := trivial"
'''


class Driver(unittest.TestCase):
    def test_driver_finds_objects_and_certificates(self):
        with tempfile.TemporaryDirectory() as tmp:
            T = Path(tmp)
            (T / "driver.py").write_text(H.CONSTRUCT_DRIVER)
            (T / "program.py").write_text(TOY)
            (T / "config.json").write_text(json.dumps({"seconds": 2, "seed": 3, "archive_in": [{"object": [1, 2, 4], "score": 3}]}))
            r = subprocess.run([sys.executable, "-I", "driver.py"], cwd=T, capture_output=True, text=True, timeout=60)
            arch = json.loads(r.stdout.split("ARCHIVE:")[1])
            self.assertGreaterEqual(arch[0]["score"], 4)
            self.assertTrue(all(a["certificate"].startswith("theorem construct_cert") for a in arch))
            self.assertTrue(any(a["how"] == "carried" or a["how"].startswith("generate") or a["how"] == "mutate" for a in arch))

    def test_toy_program_passes_safety_screen(self):
        self.assertIsNone(H.unsafe_python(TOY))


if __name__ == "__main__":
    unittest.main()
