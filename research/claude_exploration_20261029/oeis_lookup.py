"""Query OEIS for each per-k coefficient column computed by
extend_coefficient_table.py. Only meaningful on a runner with real internet
access (OEIS is not reachable through this project's own sandbox proxy at
all -- that's exactly why this step belongs in CI, not locally).

Writes oeis_matches.json: for each k, the raw OEIS search hits (if any) for
that column's sequence, so a human can judge relevance -- this script does
not itself claim a match is meaningful, only that OEIS returned it.
"""
import json
import time
import urllib.request
import urllib.parse
from pathlib import Path

TABLE_PATH = Path(__file__).parent / "coefficient_table.json"
OUT_PATH = Path(__file__).parent / "oeis_matches.json"
MIN_TERMS = 6


def columns(table):
    by_k = {}
    for n_str, row in table.items():
        n = int(n_str)
        for k_str, c in row["coefficients"].items():
            k = int(k_str)
            by_k.setdefault(k, {})[n] = c
    return by_k


def oeis_search(seq):
    q = ",".join(str(x) for x in seq)
    url = "https://oeis.org/search?" + urllib.parse.urlencode({"q": q, "fmt": "json"})
    req = urllib.request.Request(url, headers={
        # oeis.org returns 403 to the default urllib User-Agent (looks like
        # a bot to them); a normal browser-ish UA is accepted.
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) research-script/1.0 "
                      "(contact: jdh1701-lc004-same-game- repo exploration)",
    })
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = json.loads(resp.read().decode())
    except Exception as exc:  # pragma: no cover - diagnostic only
        return {"error": repr(exc)}
    if not data or data.get("results") is None:
        return {"results": []}
    hits = []
    for r in data["results"][:5]:
        hits.append({"number": r.get("number"), "name": r.get("name"),
                      "data": r.get("data")})
    return {"results": hits}


def main():
    table = json.loads(TABLE_PATH.read_text())
    cols = columns(table)
    out = {}
    for k in sorted(cols):
        ns = sorted(cols[k])
        seq = [cols[k][n] for n in ns]
        if len(seq) < MIN_TERMS:
            continue
        print(f"searching OEIS for k={k}: {seq}", flush=True)
        out[k] = {"n_range": [ns[0], ns[-1]], "sequence": seq,
                   "oeis": oeis_search(seq)}
        time.sleep(1.0)  # be polite to oeis.org
        print(json.dumps(out[k]["oeis"], indent=2), flush=True)
    OUT_PATH.write_text(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
