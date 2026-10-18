#!/usr/bin/env python3
"""Exact negative controls for using the wrong partition lattice."""
from itertools import combinations, product
import json
from pathlib import Path
from partition_count import witnesses, signed_constraints, join, matches

HERE = Path(__file__).resolve().parent


def crossing(p):
    return any(p[a] == p[c] and p[b] == p[d] and p[a] != p[b]
               for a, b, c, d in combinations(range(len(p)), 4))


def main():
    p = (0, 1, 1, 0, 2, 3, 3, 2)
    r = (0, 1, 2, 3, 3, 2, 1, 0)
    j = join(p, r)
    assert p in witnesses(8) and r in witnesses(8)
    assert not crossing(p) and not crossing(r) and crossing(j)
    assert j == (0, 1, 1, 0, 0, 1, 1, 0)
    rows = []
    for q in (2, 3):
        actual = sum(matches(p, w) or matches(r, w)
                     for w in product(range(q), repeat=8))
        correct = 2 * q**4 - q**2
        # NC closure merges these two crossing blocks into one.
        wrong = 2 * q**4 - q
        assert actual == correct != wrong
        rows.append(dict(q=q, direct_union=actual, all_partition_join=correct,
                         incorrect_noncrossing_join=wrong))
    support_rows = []
    for n in range(11):
        terms, _ = signed_constraints(witnesses(n))
        nonzero = [(p, a) for p, a in terms.items() if crossing(p)]
        assert len(nonzero) == (5 if n == 10 else 0)
        support_rows.append(dict(n=n, nonzero_crossing_terms=nonzero))
    result = dict(pair=p, nested=r, actual_join=j, negative_controls=rows,
                  signed_support_checks=support_rows, failures=0)
    (HERE / 'data/join_controls.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
