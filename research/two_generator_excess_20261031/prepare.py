"""Derive compressed six-class pair types from the COMPLETE original catalogue.

Only edges identified in both states are contracted; their global adjacency
follows from the common-gap theorem. No six-class run-shape conjecture is used.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/ten_attacks_20261030'))
from core import catalogue, join


def normalize(p):
    names = {}
    return tuple(names.setdefault(a, len(names)) for a in p)


def prepare():
    cs = catalogue(6)
    out, original = set(), []
    for ia, ib in combinations(range(len(cs)), 2):
        a, b = cs[ia], cs[ib]
        if len(set(join(a, b))) != 1:
            continue
        common = {i for i in range(6)
                  if a[i] == a[(i+1) % 6] and b[i] == b[(i+1) % 6]}
        assert len(common) in (0, 2)
        assert all((i+1) % 6 not in common for i in common)
        starts = [i for i in range(6) if (i-1) % 6 not in common]
        original.append({'states': [ia, ib], 'common_edges': sorted(common)})
        for t in range(len(starts)):
            ss = starts[t:] + starts[:t]
            w = tuple((ss[(i+1) % len(ss)]-x) % 6 for i, x in enumerate(ss))
            upper, lower = sorted((normalize(tuple(a[i] for i in ss)),
                                   normalize(tuple(b[i] for i in ss))))
            out.add((w, upper, lower))
    assert len(original) == 22 and len(out) == 17
    assert Counter(len(x[0]) for x in out) == {4: 10, 6: 7}
    with (HERE / 'types.txt').open('w') as f:
        for w, a, b in sorted(out):
            assert sum(w) == 6
            for s in (a, b):
                expanded = normalize(tuple(c for c, k in zip(s, w) for _ in range(k)))
                assert expanded in cs
            print(len(w), *w, *a, *b, file=f)
    with (HERE / 'catalogues.txt').open('w') as f:
        for n in (5, 6):
            for s in catalogue(n):
                print(n, *s, file=f)
    (HERE / 'preparation.json').write_text(json.dumps({
        'original_full_join_pairs': original,
        'compressed_unordered_pair_types': len(out),
        'types_by_vertices': dict(Counter(len(x[0]) for x in out))
    }, indent=2, sort_keys=True)+'\n')


if __name__ == '__main__':
    prepare()
