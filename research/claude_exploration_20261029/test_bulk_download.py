"""One-shot test: is OEIS's bulk data dump reachable from CI even though the
live /search API returns 403 on every query? If oeis.org blocks by IP range
wholesale, this fails the same way; if the block is somehow endpoint- or
query-shape-specific, this succeeds and unlocks fully offline OEIS lookup
(download once, grep locally, no more live queries at all).
"""
import urllib.request

UA = ("Mozilla/5.0 (X11; Linux x86_64) research-script/1.0 "
      "(contact: jdh1701-lc004-same-game- repo exploration)")

urls = [
    "https://oeis.org/stripped.gz",
    "https://oeis.org/",
]

for url in urls:
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read(200)
            print(f"{url}: HTTP {resp.status}, first bytes: {data[:80]!r}")
    except Exception as exc:
        print(f"{url}: FAILED {exc!r}")
