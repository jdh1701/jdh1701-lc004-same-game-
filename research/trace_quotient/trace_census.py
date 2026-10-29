#!/usr/bin/env python3
"""Trace-quotient census for the ordinary one-dimensional Same Game.

For every winning labeled word over q colors and length n (exhaustive), with
moves identified by the set of ORIGINAL cell positions they delete:

  P  number of complete successful deletion paths;
  K  number of deletion schemes: the set of blocks a path deletes, order
     forgotten;
  T  number of trace classes: connected components of successful paths under
     swapping two adjacent moves (swapping is allowed whenever the swapped
     sequence is still a successful path; the blocks, hence the final state,
     are unchanged).

Checks:
  * every scheme is a noncrossing partition of the positions;
  * T == K (all orders of one scheme are connected by adjacent swaps);
  * distribution of K over winning words, versus P == 1.

No dependencies; deterministic.  Usage:
    python3 trace_census.py --ranges 2:12,3:10,4:8
"""
import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import product


def moves(state):
    """state: tuple of (pos, color). Yield (block, successor)."""
    i = 0
    while i < len(state):
        j = i + 1
        while j < len(state) and state[j][1] == state[i][1]:
            j += 1
        if j - i >= 2:
            yield frozenset(p for p, _ in state[i:j]), state[:i] + state[j:]
        i = j


@lru_cache(maxsize=None)
def path_count(state):
    if not state:
        return 1
    return sum(path_count(t) for _, t in moves(state))


@lru_cache(maxsize=None)
def schemes(state):
    """Frozenset of schemes (frozensets of blocks) that clear the state."""
    if not state:
        return frozenset([frozenset()])
    out = set()
    for b, t in moves(state):
        for sch in schemes(t):
            out.add(sch | {b})
    return frozenset(out)


def orders_for_scheme(word, scheme):
    """All successful paths realizing the given scheme."""
    res = []

    def rec(state, used, seq):
        if not state:
            res.append(tuple(seq))
            return
        for b, t in moves(state):
            if b in scheme and b not in used:
                rec(t, used | {b}, seq + [b])

    rec(tuple(enumerate(word)), frozenset(), [])
    return res


def components(orders):
    valid = set(orders)
    seen, comps = set(), 0
    for o in orders:
        if o in seen:
            continue
        comps += 1
        stack = [o]
        seen.add(o)
        while stack:
            x = stack.pop()
            for k in range(len(x) - 1):
                y = x[:k] + (x[k + 1], x[k]) + x[k + 2:]
                if y in valid and y not in seen:
                    seen.add(y)
                    stack.append(y)
    return comps


def noncrossing(scheme):
    spans = [(min(b), max(b), b) for b in scheme]
    for a1, a2, A in spans:
        for b1, b2, B in spans:
            if A is B:
                continue
            # a cell of B strictly inside A's span forces all of B inside it
            if any(a1 < x < a2 for x in B) and not (a1 < b1 and b2 < a2):
                return False
    return True


def census(q, n):
    stats = Counter()
    kdist, tdist = Counter(), Counter()
    joint = Counter()  # (P==1, K==1)
    examples = {}
    for word in product(range(q), repeat=n):
        start = tuple(enumerate(word))
        P = path_count(start)
        if P == 0:
            continue
        stats["W"] += 1
        S = schemes(start)
        K = len(S)
        T = 0
        for sch in S:
            if not noncrossing(sch):
                stats["crossing_schemes"] += 1
                examples.setdefault("crossing", word)
            T += components(orders_for_scheme(word, sch))
        if T != K:
            stats["T_ne_K"] += 1
            examples.setdefault("T_ne_K", (word, T, K))
        kdist[K] += 1
        tdist[T] += 1
        joint[(P == 1, K == 1)] += 1
        if K > 1:
            examples.setdefault(f"K={K}", "".join("abcdefgh"[c] for c in word))
    path_count.cache_clear()
    schemes.cache_clear()
    return {
        "q": q,
        "n": n,
        "W": stats["W"],
        "U_paths_eq_1": joint[(True, True)] + joint[(True, False)],
        "K_eq_1": joint[(True, True)] + joint[(False, True)],
        "P_gt_1_but_K_eq_1": joint[(False, True)],
        "T_ne_K_words": stats["T_ne_K"],
        "crossing_schemes": stats["crossing_schemes"],
        "K_distribution": dict(sorted(kdist.items())),
        "examples": {k: v for k, v in sorted(examples.items())[:6]},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranges", default="2:12,3:10,4:8")
    args = ap.parse_args()
    for part in args.ranges.split(","):
        q, nmax = map(int, part.split(":"))
        for n in range(1, nmax + 1):
            print(json.dumps(census(q, n)), flush=True)


if __name__ == "__main__":
    main()
