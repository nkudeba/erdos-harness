"""Cache the forum thread and proof-claims page for chosen problems.

The main problem page is not the whole record. #488's claimed counterexample lives only on its proof-claims
page, and #287's "no counterexample below 4e19" certificates live only in its forum thread. The ranker reads
whatever this has cached, so a claimed resolution or a published exhaustive check stops being invisible.

    python3 atlas-data/fetch_forum.py --problems 488 287 848
    python3 atlas-data/fetch_forum.py --finite-certificate      # every open falsifiable/verifiable/decidable

Cached under atlas-data/forum/<n>.json. Re-fetch with --refresh. Polite by default: one request at a time
with a pause, browser UA (the site 403s generic fetchers).
"""
import argparse, html, json, re, sys, time, urllib.error, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT / "atlas-data" / "forum"
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0 Safari/537.36"


def text_of(page: str) -> str:
    h = re.sub(r"(?s)<(script|style)[^>]*>.*?</\1>", "", page)
    h = re.sub(r"<br\s*/?>|</(p|div|li|h\d|tr|article)>", "\n", h)
    t = html.unescape(re.sub(r"<[^>]+>", "", h))
    return re.sub(r"\n\s*\n+", "\n", re.sub(r"[ \t]+", " ", t)).strip()


def fetch(url: str, timeout: int = 30) -> str | None:
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "text/html"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read().decode(errors="replace")
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError):
        return None   # a missing thread is normal; the caller records what it got


def capture(pid: int, pause: float = 1.0) -> dict:
    thread = fetch(f"https://www.erdosproblems.com/forum/thread/{pid}")
    time.sleep(pause)
    claims = fetch(f"https://www.erdosproblems.com/forum/thread/{pid}/proof-claims")
    time.sleep(pause)
    record = {"problem": pid, "fetched": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "thread": text_of(thread)[:200000] if thread else "",
              "claims": text_of(claims)[:60000] if claims else "",
              "thread_available": thread is not None, "claims_available": claims is not None}
    return record


def load_cached(pid: int) -> dict | None:
    f = CACHE / f"{pid}.json"
    try:
        return json.loads(f.read_text())
    except (OSError, ValueError):
        return None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--problems", nargs="*", type=int, default=[])
    ap.add_argument("--finite-certificate", action="store_true",
                    help="every unsolved problem the catalogue calls falsifiable/verifiable/decidable")
    ap.add_argument("--reviewed", action="store_true", help="every problem in reviewed.json")
    ap.add_argument("--refresh", action="store_true", help="re-fetch even when cached")
    ap.add_argument("--pause", type=float, default=1.0)
    args = ap.parse_args()

    ids = set(args.problems)
    if args.finite_certificate or args.reviewed:
        try:
            ranked = json.loads((ROOT / "atlas-data" / "rankings.json").read_text())["problems"]
        except (OSError, ValueError, KeyError):
            print("rankings.json is required for --finite-certificate/--reviewed", file=sys.stderr)
            return 2
        if args.finite_certificate:
            ids |= {r["id"] for r in ranked
                    if r["status"] == "Unsolved" and r["state"] in ("falsifiable", "verifiable", "decidable")}
        if args.reviewed:
            ids |= {int(k) for k in json.loads((ROOT / "atlas-data" / "reviewed.json").read_text())}
    if not ids:
        print("nothing to fetch: pass --problems, --finite-certificate or --reviewed", file=sys.stderr)
        return 2

    CACHE.mkdir(parents=True, exist_ok=True)
    fetched = skipped = 0
    for pid in sorted(ids):
        if not args.refresh and load_cached(pid):
            skipped += 1
            continue
        record = capture(pid, args.pause)
        (CACHE / f"{pid}.json").write_text(json.dumps(record, ensure_ascii=False, indent=1) + "\n")
        fetched += 1
        flags = "".join(["t" if record["thread"] else "-", "c" if record["claims"] else "-"])
        print(f"  #{pid} [{flags}] thread {len(record['thread'])}b claims {len(record['claims'])}b", flush=True)
    print(f"fetched {fetched}, already cached {skipped}; run `python3 atlas-data/rank_problems.py` to use them")
    return 0


if __name__ == "__main__":
    sys.exit(main())
