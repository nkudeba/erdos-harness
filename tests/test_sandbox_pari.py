"""PARI/GP (cypari2) in the research sandbox, and the three layers that keep model-written scripts contained
(2026-10-08). Both v6 full runs stopped at a significance-2 step that needed computational number theory: #686's
Prym-Chabauty and #366's Thue equations. Each session wrote "infeasible without PARI/Magma".

PARI can run shell commands and read and write files, and a script can build a function's name at runtime, which no
static screen sees. So:
1. the static screen names PARI's shell, file and environment functions, and numpy's file readers;
2. PARI runs in secure mode, set before the script, which refuses system, extern, write and install;
3. on macOS a Seatbelt profile, enforced by the kernel, refuses network access, every process but the interpreter,
   reads under the home directory outside the script's folder, and writes outside it.
The numpy file readers were an open hole before this change: `np.loadtxt(path)` could read the benchmark's answers."""
import os, subprocess, sys, tempfile, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

try:
    import cypari2                                       # noqa: F401
    HAVE_PARI = True
except ImportError:
    HAVE_PARI = False
SEATBELT = sys.platform == "darwin" and Path("/usr/bin/sandbox-exec").exists()


class Screen(unittest.TestCase):
    def test_pari_is_allowed_and_its_dangerous_functions_are_not(self):
        self.assertIn("cypari2", H.ALLOWED_PY_MODULES)
        self.assertIn("cypari2", H.EXPLORE_MODULES)
        ok = "from cypari2 import Pari\npari = Pari()\nprint(pari('thue(thueinit(x^3-2,1),1)'))\n"
        self.assertIsNone(H.unsafe_python(ok))
        for bad in ('pari(\'system("ls")\')', "pari.readstr('/etc/hosts')", "pari('readstr(\"x\")')",
                    "pari.default('secure', 0)", "pari('extern(\"ls\")')", "pari.install('f', 'L')",
                    "pari('write(\"/tmp/x\", 1)')", "pari.getenv('HOME')", "pari('fileopen(\"x\")')"):
            self.assertIsNotNone(H.unsafe_python("from cypari2 import Pari\npari = Pari()\n" + bad), bad)

    def test_numpy_file_readers_are_refused(self):
        for bad in ("np.loadtxt('x')", "np.genfromtxt('x')", "np.fromfile('x')", "np.load('x.npy')"):
            self.assertIsNotNone(H.unsafe_python("import numpy as np\n" + bad, H.EXPLORE_MODULES, H.EXPLORE_FORBIDDEN), bad)
        self.assertIsNone(H.unsafe_python("import json\nprint(json.loads('[1]'))"))      # loads is not load(

    def test_a_longer_script_cap_reaches_the_runner_and_the_cli(self):
        self.assertIn("SECONDS = 600", H.explore_runner_source(600))
        self.assertIn(f"SECONDS = {H.EXPLORE_SECONDS}", H.explore_runner_source())
        seen = {}

        class B(H.ClaudeCliBackend):
            def _run(self, purpose, prompt, extra, cwd, effort_override=None, budget_override=None, env_extra=None):
                seen["env"] = env_extra
                return "ok"
        b = B.__new__(B)
        b.complete_explore("p", "x", Path("/tmp"), 5, script_seconds=600)
        self.assertEqual(seen["env"], {"BASH_DEFAULT_TIMEOUT_MS": "660000", "BASH_MAX_TIMEOUT_MS": "660000"})
        b.complete_explore("p", "x", Path("/tmp"), 5)
        self.assertIsNone(seen["env"])

    def test_the_session_prompt_names_pari(self):
        self.assertIn("cypari2", H.SESSION_PROMPT)
        self.assertIn("thueinit", H.SESSION_PROMPT)


@unittest.skipUnless(SEATBELT, "macOS sandbox-exec")
class Seatbelt(unittest.TestCase):
    def test_the_profile_names_the_scripts_folder(self):
        argv = H.sandbox_argv(Path("/tmp/somewhere/s.py"))
        self.assertEqual(argv[:2], ["/usr/bin/sandbox-exec", "-p"])
        self.assertIn(f'(subpath "{Path("/tmp/somewhere").resolve()}")', argv[2])     # /private/tmp on macOS
        self.assertIn("(deny network*)", argv[2])
        runner = H.explore_runner_source()
        self.assertIn(H.SANDBOX_DIR_TOKEN, runner)                # filled in with the runner's own folder at run time
        self.assertIn("replace(DIR_TOKEN, str(here))", runner)

    def _run(self, code: str, folder: Path) -> subprocess.CompletedProcess:
        (folder / "s.py").write_text(code)
        return subprocess.run(H.sandbox_argv(folder / "s.py"), capture_output=True, text=True, timeout=60,
                              cwd=str(folder), env={"PATH": "/usr/bin:/bin", "HOME": str(folder)})

    @unittest.skipUnless(HAVE_PARI, "cypari2")
    def test_pari_works_and_a_runtime_name_cannot_escape(self):
        target = Path(H.__file__).resolve().parent / "CLAUDE.md"   # a file under the home directory
        with tempfile.TemporaryDirectory(dir=str(Path(H.__file__).resolve().parent / "runs")) as tmp:
            folder = Path(tmp)
            r = self._run("from cypari2 import Pari\npari = Pari()\nprint(pari('thue(thueinit(x^3-2,1),1)'))\n"
                          "for code in ('read' + 'str(\"%s\")', 'sys' + 'tem(\"touch %s\")'):\n"
                          "    try:\n        print('ALLOWED', str(pari(code))[:40])\n"
                          "    except Exception as e:\n        print('blocked', str(e)[:60])\n"
                          % (target, folder / "escaped"), folder)
            self.assertEqual(r.returncode, 0, r.stderr[-400:])
            self.assertIn("[[-1, -1], [1, 0]]", r.stdout)
            self.assertNotIn("ALLOWED", r.stdout)
            self.assertFalse((folder / "escaped").exists())

    def test_reads_outside_the_folder_and_the_network_are_refused(self):
        repo = Path(H.__file__).resolve().parent
        with tempfile.TemporaryDirectory(dir=str(repo / "runs")) as tmp:
            folder = Path(tmp)
            r = self._run("import socket\nfor f in (lambda: len(__builtins__.open(%r).read()),\n"
                          "          lambda: socket.create_connection(('example.com', 80), timeout=5)):\n"
                          "    try:\n        print('ALLOWED', f())\n    except Exception as e:\n"
                          "        print('blocked', type(e).__name__)\n" % str(repo / "CLAUDE.md"), folder)
            self.assertEqual(r.returncode, 0, r.stderr[-400:])
            self.assertEqual(r.stdout.count("blocked"), 2, r.stdout)


if __name__ == "__main__":
    unittest.main()
