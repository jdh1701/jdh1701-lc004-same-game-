#!/usr/bin/env python3
"""Does every winning word have a canonical deletion scheme?

For each winning word, with S its set of schemes (see trace_census.py), test:
  * a unique scheme with the most blocks (finest);
  * a unique scheme with the fewest blocks (coarsest);
  * whether that unique finest scheme refines every other scheme;
  * whether that unique coarsest scheme is refined by every other scheme.
Usage: python3 canonical_scheme.py --ranges 2:14,3:11,4:9
"""
import argparse
import json
from collections import Counter
from itertools import product

from trace_census import schemes


def refines(a, b):
    """Every block of a lies inside a block of b."""
    return all(any(x <= y for y in b) for x in a)


def show(word, sch):
    lab = "abcdefgh"
    return "".join(lab[c] for c in word) + " " + str(
        sorted(sorted(b) for b in sch))


def run(q, n):
    st = Counter()
    ex = {}
    for word in product(range(q), repeat=n):
        S = list(schemes(tuple(enumerate(word))))
        if not S:
            continue
        st["W"] += 1
        if len(S) == 1:
            continue
        st["multi"] += 1
        mx = max(len(s) for s in S)
        mn = min(len(s) for s in S)
        fine = [s for s in S if len(s) == mx]
        coarse = [s for s in S if len(s) == mn]
        if len(fine) == 1:
            if all(refines(fine[0], s) for s in S):
                st["finest_refines_all"] += 1
            else:
                ex.setdefault("finest_not_refining", [show(word, s) for s in S])
        else:
            st["finest_not_unique"] += 1
            ex.setdefault("finest_not_unique", [show(word, s) for s in S])
        if len(coarse) == 1:
            if all(refines(s, coarse[0]) for s in S):
                st["coarsest_refined_by_all"] += 1
            else:
                ex.setdefault("coarsest_not_refined", [show(word, s) for s in S])
        else:
            st["coarsest_not_unique"] += 1
            ex.setdefault("coarsest_not_unique", [show(word, s) for s in S])
    schemes.cache_clear()
    return {"q": q, "n": n, **st, "examples": ex}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranges", default="2:14,3:11,4:9")
    for part in ap.parse_args().ranges.split(","):
        q, nmax = map(int, part.split(":"))
        for n in range(2, nmax + 1):
            print(json.dumps(run(q, n)), flush=True)
