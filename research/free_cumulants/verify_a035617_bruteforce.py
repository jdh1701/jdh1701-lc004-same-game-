"""Fully independent brute-force verification of A035617 (ternary
maximal-run-deletion winning-word count) for small N, with NO use of the
project's FusionStack automaton or any of its machinery -- a from-scratch
direct simulation of the actual game rule, to cross-check both the OEIS
terms themselves and (indirectly) the correctness of the automaton
reformulation reviewed in research/WORKBOARD.md on 2026-11-04.

Rule: repeatedly delete any ONE maximal run of >=2 identical adjacent
symbols (the whole run, not just a pair/triple) from the word; the word is
a winner iff some sequence of such deletions reaches the empty word.
Memoized DFS/BFS over reachable words from each candidate, for all words
of length <= N over a 3-letter alphabet.
"""
import itertools
from functools import lru_cache

def delete_one_run(w):
    """All words obtainable by deleting exactly one maximal run (length>=2)
    of identical adjacent symbols from w."""
    n = len(w)
    out = []
    i = 0
    while i < n:
        j = i
        while j < n and w[j] == w[i]:
            j += 1
        if j - i >= 2:
            out.append(w[:i] + w[j:])
        i = j
    return out

@lru_cache(maxsize=None)
def is_winning(w):
    if not w:
        return True
    return any(is_winning(nxt) for nxt in delete_one_run(w))

def count_winning(n, q=3):
    total = 0
    for w in itertools.product(range(q), repeat=n):
        if is_winning(w):
            total += 1
    return total

expected = {0:1,1:0,2:3,3:3,4:15,5:33,6:105,7:297,8:879,9:2631,10:7833,
            11:23697,12:71385,13:216765}

for n in range(0, 14):
    is_winning.cache_clear()
    got = count_winning(n)
    exp = expected.get(n)
    status = "OK" if got == exp else f"MISMATCH (expected {exp})"
    print(f"n={n:2d}  W={got:>10}  {status}")

import time
expected2 = {14:657849, 15:2003151, 16:6103743}
for n in (14, 15):
    is_winning.cache_clear()
    t0 = time.time()
    got = count_winning(n)
    dt = time.time() - t0
    exp = expected2.get(n)
    status = "OK" if got == exp else f"MISMATCH (expected {exp})"
    print(f"n={n:2d}  W={got:>10}  {status}  ({dt:.1f}s)")
