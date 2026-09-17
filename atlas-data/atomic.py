"""Crash-safe, concurrency-safe writes for the Atlas's shared files.

`reviewed.json` is the Atlas's memory: 83 assessed problems, and the only place the qualitative half of
what we have learned lives. `record_finding.py` used to mutate it with a bare read-modify-write --
`json.loads(read_text())`, mutate, `write_text(...)` -- which has two failure modes that both destroy
recorded findings rather than merely inconveniencing a run:

  * **Lost update.** Two agents recording findings for DIFFERENT problems at the same time each read the
    same dict, each add their own key, and whichever writes second silently erases the other's entry. The
    loss is invisible: both processes print success.
  * **Truncation.** `write_text` opens with O_TRUNC, so a crash, a full disk, or a Ctrl-C between the
    truncate and the final byte leaves the file short -- and a short JSON file is an unparseable file, so
    the next `load()` falls back to `{}` and the whole Atlas reads as empty.

Both are one-line fixes that nothing else in the codebase has to know about: take an exclusive lock for
the whole read-modify-write, and make the write itself atomic by renaming a fully-written temp file over
the target. `os.replace` is atomic within a filesystem, so a reader either sees the old file or the new
one, never a half-written one.

This matters more here than the usual "be careful with concurrency" boilerplate, because the harness is
explicitly designed to run things at the same time (`--open` attacks both directions concurrently) and
because the project's own instructions say the Atlas is what decides which problem we attack next. A
finding that is silently dropped is exactly the failure the Atlas exists to prevent.
"""
import contextlib, fcntl, json, os, tempfile
from pathlib import Path


def atomic_write(path: Path, text: str) -> None:
    """Replace `path` with `text` in one indivisible step (write temp in the same dir, then rename)."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), prefix=f".{path.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())          # the bytes are on disk before anything points at them
        os.replace(tmp, path)             # atomic within a filesystem
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(tmp)
        raise


def atomic_write_json(path: Path, obj, **kw) -> None:
    kw.setdefault("ensure_ascii", False)
    atomic_write(path, json.dumps(obj, **kw) + "\n")


@contextlib.contextmanager
def locked(path: Path):
    """Hold an exclusive lock covering a read-modify-write of `path`.

    The lock lives on a sibling `.<name>.lock` rather than on `path` itself, because `atomic_write`
    renames a new file over `path` -- a lock held on the old inode would protect nothing.
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    lock = path.parent / f".{path.name}.lock"
    with open(lock, "w") as f:
        fcntl.flock(f.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f.fileno(), fcntl.LOCK_UN)
