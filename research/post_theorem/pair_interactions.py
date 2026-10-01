#!/usr/bin/env python3
"""Exact two-successful-first-move interaction census on ordinary words."""
import argparse
import csv
import sys
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path

here = Path(__file__).resolve()
dirs = [here.parents[1]/"public-lc004"/"scripts",
        here.parents[2]/"scripts", here.parents[1]/"scripts"]
root = next(d for d in dirs if (d/"exhaustive_verify.py").exists())
sys.path.insert(0, str(root))
import exhaustive_verify as ref


@lru_cache(None)
def win(s):
    return not s or any(win(t) for _, t in ref.run_moves(s))


def transported(s, first, second):
    """Index of the same original run, or None if absorbed by first bridge."""
    bridge = (0 < first < len(s)-1 and
              s[first-1][0] == s[first+1][0])
    if bridge:
        if second == first-1 or second == first+1:
            return None
        return second if second < first-1 else second-2
    return second if second < first else second-1


def census(q, n):
    out = Counter()
    for w in product(range(q), repeat=n):
        s = ref.encode_word(w)
        good = [i for i, t in ref.run_moves(s) if win(t)]
        for p, i in enumerate(good):
            for j in good[p+1:]:
                dist = min(j-i, 4)
                a, b = transported(s, i, j), transported(s, j, i)
                ti, tj = ref.run_successor(s, i), ref.run_successor(s, j)
                if a is None or b is None:
                    kind = "absorbed_original_run"
                else:
                    x = ref.run_successor(ti, a)
                    y = ref.run_successor(tj, b)
                    kind = "exact_commute" if x == y and x is not None else (
                           "legal_but_different" if x is not None and y is not None
                           else "one_unavailable")
                out[(dist, kind)] += 1
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranges", default="3:13,4:11")
    ap.add_argument("--out", default=str(here.parent/"results"/"pair_interactions.csv"))
    args = ap.parse_args()
    rows = []
    for spec in args.ranges.split(","):
        q, n = map(int, spec.split(":"))
        counts = census(q, n)
        for (dist, kind), count in sorted(counts.items()):
            rows.append(dict(q=q, n=n, distance_class="4+" if dist==4 else str(dist),
                             interaction=kind, pairs=count))
        print(q, n, sum(counts.values()), dict(counts), flush=True)
    with open(args.out, "w", newline="") as f:
        wr = csv.DictWriter(f, fieldnames=["q","n","distance_class","interaction","pairs"])
        wr.writeheader()
        wr.writerows(rows)


if __name__ == "__main__":
    main()
