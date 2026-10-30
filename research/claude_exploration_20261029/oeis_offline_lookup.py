"""Offline OEIS lookup: oeis.org's live /search endpoint returns 403 to
every query from GitHub Actions runners (confirmed, multiple attempts,
oeis_lookup.py's receipts), but the bare domain and the bulk data dump
(oeis.org/stripped.gz, ~50MB compressed, every sequence's first terms) both
return HTTP 200 (confirmed in test_bulk_download.py's CI run). So: download
the dump once per run and grep it in memory instead of live-querying.

stripped.gz format: one line per sequence, "A000045 ,0,1,1,2,3,5,8,13,...,"
(leading comma, trailing comma, terms as plain integers). A match requires
our sequence to appear as a contiguous comma-separated substring.
"""
import gzip
import json
import urllib.request
from pathlib import Path

TABLE_PATH = Path(__file__).parent / "coefficient_table.json"
OUT_PATH = Path(__file__).parent / "oeis_matches.json"
MIN_TERMS = 6
DUMP_URL = "https://oeis.org/stripped.gz"
UA = ("Mozilla/5.0 (X11; Linux x86_64) research-script/1.0 "
      "(contact: jdh1701-lc004-same-game- repo exploration)")


def columns(table):
    by_k = {}
    for n_str, row in table.items():
        n = int(n_str)
        for k_str, c in row["coefficients"].items():
            k = int(k_str)
            by_k.setdefault(k, {})[n] = c
    return by_k


def fetch_dump():
    req = urllib.request.Request(DUMP_URL, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=180) as resp:
        chunks = []
        while True:
            chunk = resp.read(1 << 20)
            if not chunk:
                break
            chunks.append(chunk)
        raw = gzip.decompress(b"".join(chunks))
    return raw.decode("ascii", errors="replace")


def search_dump(dump_text, seq):
    needle = "," + ",".join(str(x) for x in seq) + ","
    hits = []
    for line in dump_text.splitlines():
        if not line or line.startswith("#"):
            continue
        idx = line.find(needle)
        if idx == -1:
            continue
        aid = line.split(",", 1)[0].strip()
        hits.append(aid)
        if len(hits) >= 10:
            break
    return hits


def main():
    print(f"::notice title=oeis-debug::CWD={Path.cwd()} OUT_PATH={OUT_PATH.resolve()}", flush=True)
    table = json.loads(TABLE_PATH.read_text())
    cols = columns(table)
    print(f"::notice title=oeis-debug::cols sizes: "
          f"{ {k: len(v) for k, v in sorted(cols.items())} }", flush=True)
    print("fetching OEIS bulk dump (oeis.org/stripped.gz)...", flush=True)
    dump_text = fetch_dump()
    print(f"dump fetched: {len(dump_text)} chars, "
          f"{dump_text.count(chr(10))} lines", flush=True)
    out = {}
    # The all-five connected-kernel survivor sequence (j=2..5 class counts),
    # cross-validated by two independent implementations this session.
    # Only 4 terms -- below the general MIN_TERMS filter below, but worth
    # checking on its own since it's the sequence of actual interest.
    all_five = [5, 35, 415, 6455]
    hits = search_dump(dump_text, all_five)
    out["all_five_survivors"] = {"sequence": all_five, "oeis_ids": hits}
    print(f"all-five survivor sequence {all_five} -> OEIS matches: "
          f"{hits or 'NONE'}", flush=True)
    # Write immediately so all_five_survivors is on disk even if a later
    # per-k iteration throws (previously this key only existed in-memory
    # until the first loop write, so an empty/short cols dict meant it was
    # silently dropped -- this is almost certainly why it never landed).
    OUT_PATH.write_text(json.dumps(out, indent=2))
    print(f"::notice title=oeis-debug::wrote {OUT_PATH.resolve()} after all_five_survivors, "
          f"{OUT_PATH.stat().st_size} bytes", flush=True)
    for k in sorted(cols):
        ns = sorted(cols[k])
        seq = [cols[k][n] for n in ns]
        if len(seq) < MIN_TERMS:
            print(f"::notice title=oeis-debug::skipping k={k}, only {len(seq)} terms "
                  f"(< MIN_TERMS={MIN_TERMS})", flush=True)
            continue
        hits = search_dump(dump_text, seq)
        out[k] = {"n_range": [ns[0], ns[-1]], "sequence": seq, "oeis_ids": hits}
        OUT_PATH.write_text(json.dumps(out, indent=2))  # sort_keys=True crashes: out mixes str ("all_five_survivors") and int keys
        print(f"k={k} seq={seq} -> OEIS matches: {hits or 'NONE'}", flush=True)
    print(f"::notice title=oeis-debug::final out keys: {list(out.keys())}", flush=True)
    print("done.", flush=True)


if __name__ == "__main__":
    import sys
    import traceback
    try:
        main()
    except Exception:
        # Raw log download is blocked from the sandbox, so print the
        # traceback as a notice annotation instead of just dying quietly.
        tb = traceback.format_exc()
        for line in tb.splitlines():
            print(f"::notice title=oeis-offline-error::{line}", flush=True)
        sys.exit(1)
