#!/usr/bin/env python3
"""Exact signed equality-partition counting; independent of deletion paths.

Witnesses are noncrossing partitions with block sizes two or three.  Their
equality events overlap.  Incremental inclusion-exclusion combines equal
partition joins and drops zero coefficients.  This is not a claimed efficient
solution of the general enumeration problem, nor a Lean-verified executable.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import csv
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'checkpoint_2026_10_17'))
from experiments import grammar_solvable, raw_paths, restricted_growth


def canonical(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)


@lru_cache(None)
def witnesses(n):
    """Decompose by the block containing the leftmost position.

    Distinct tags keep different blocks independent.  Canonical labelling
    removes all naming choices.  Suffix recursion removes SS-association.
    """
    if n == 0:
        return ((),)
    out = set()
    for a in range(n - 1):
        b = n - 2 - a
        for x, y in product(witnesses(a), witnesses(b)):
            out.add(canonical(((0, 0),) + tuple((1, c) for c in x)
                              + ((0, 0),) + tuple((2, c) for c in y)))
    for a in range(n - 2):
        for b in range(n - 2 - a):
            c = n - 3 - a - b
            for x, y, z in product(witnesses(a), witnesses(b), witnesses(c)):
                out.add(canonical(((0, 0),) + tuple((1, t) for t in x)
                                  + ((0, 0),) + tuple((2, t) for t in y)
                                  + ((0, 0),) + tuple((3, t) for t in z)))
    return tuple(sorted(out))


def join(p, r):
    """Join in the lattice of ALL equivalence relations, not NC closure."""
    assert len(p) == len(r)
    parent = list(range(len(p)))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for word in (p, r):
        first = {}
        for i, c in enumerate(word):
            j = first.setdefault(c, i)
            parent[root(i)] = root(j)
    return canonical(tuple(root(i) for i in range(len(p))))


def matches(p, w):
    labels = {}
    return all(labels.setdefault(c, x) == x for c, x in zip(p, w))


def signed_constraints(patterns):
    coeff = {}
    peak = 0
    for p in patterns:
        delta = Counter({p: 1})
        for r, a in coeff.items():
            delta[join(r, p)] -= a
        for r, a in delta.items():
            coeff[r] = coeff.get(r, 0) + a
            if not coeff[r]:
                del coeff[r]
        peak = max(peak, len(coeff))
    return coeff, peak


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, default=12)
    ap.add_argument('--word-check-n', type=int, default=8)
    args = ap.parse_args()
    orbit_rows = list(csv.DictReader((HERE.parent / 'checkpoint_2026_10_17'
                                     / 'data/orbit_polynomials.csv').open()))
    orbit_counts = {(int(r['n']), int(r['k'])): int(r['solvable_orbits'])
                    for r in orbit_rows}
    rows, checks = [], Counter()
    for n in range(args.max_n + 1):
        start = time.monotonic()
        patterns = witnesses(n)
        # Block sizes and canonical labels are explicit structural controls.
        assert all(all(v in (2, 3) for v in Counter(p).values()) for p in patterns)
        assert all(p == canonical(p) and len(p) == n for p in patterns)
        coeff, peak = signed_constraints(patterns)
        poly = Counter()
        for p, a in coeff.items():
            poly[len(set(p))] += a
        poly = {k: a for k, a in sorted(poly.items()) if a}
        # Pointwise identity includes losing words and words with many witnesses.
        if n <= args.word_check_n:
            for w in restricted_growth(n):
                matched = any(matches(p, w) for p in patterns)
                signed = sum(a for p, a in coeff.items() if matches(p, w))
                assert signed == int(matched) == int(grammar_solvable(w))
                assert matched == bool(raw_paths(w)), ('raw', w)
                checks['equality_types'] += 1
        # Existing independent raw/run orbit enumeration, not fitted samples.
        if n <= 12:
            for q in range(0, 9):
                expected = 0
                falling = 1
                for k in range(n // 2 + 1):
                    if k:
                        falling *= q - k + 1
                    expected += orbit_counts.get((n, k), 0) * falling
                got = sum(a * q**k for k, a in poly.items())
                assert got == expected, ('orbit polynomial', n, q, got, expected)
                checks['alphabet_evaluations'] += 1
        row = dict(n=n, witnesses=len(patterns), signed_join_terms=len(coeff),
                   peak_terms=peak, polynomial=poly,
                   q3=sum(a * 3**k for k, a in poly.items()),
                   seconds=time.monotonic() - start)
        rows.append(row)
        print(json.dumps(row), flush=True)
        (HERE / 'data/partition_counts.json').write_text(json.dumps(
            {'rows': rows, 'checks': dict(checks), 'failures': 0}, indent=2) + '\n')
        raw_paths.cache_clear()
        grammar_solvable.cache_clear()
    print(json.dumps({'checks': dict(checks), 'failures': 0}), flush=True)


if __name__ == '__main__':
    main()
