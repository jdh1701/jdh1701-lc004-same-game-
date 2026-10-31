"""Exhaust all 252 labelled interleavings without orbit reduction.

This is finite evidence, not a Lean proof of the local geometry theorem.
Crossing is defined directly by ordered endpoints, independently of core.py.
"""
import itertools
import json
from pathlib import Path

PAIRS = tuple(itertools.combinations(range(5), 2))


def cross(a, b):
    return any(u < x < v < y or x < u < y < v
               for u, v in itertools.combinations(sorted(a), 2)
               for x, y in itertools.combinations(sorted(b), 2))


def split(group, choice):
    pair = tuple(group[i] for i in PAIRS[choice])
    return pair, tuple(x for x in group if x not in pair)


def majority(a, b, c):
    return b if b == c else a


def main():
    rows = []
    triples = 0
    for left in itertools.combinations(range(10), 5):
        right = tuple(i for i in range(10) if i not in left)
        blocks_l = [split(left, i) for i in range(10)]
        blocks_r = [split(right, i) for i in range(10)]
        relation = set()
        for x, y in itertools.product(range(10), repeat=2):
            blocks = blocks_l[x] + blocks_r[y]
            if not any(cross(a, b) for a, b in itertools.combinations(blocks, 2)):
                relation.add((x, y))
        # Conservative majority keeps the same ten-choice labels; no relabelling.
        for a, b, c in itertools.product(relation, repeat=3):
            triples += 1
            assert (majority(a[0], b[0], c[0]),
                    majority(a[1], b[1], c[1])) in relation
        covers = [(p, q) for p, q in itertools.product(range(10), repeat=2)
                  if all(x == p or y == q for x, y in relation)]
        crossing = cross(left, right)
        if crossing:
            assert covers
        # Each independent five-point class has exactly five internally NC splits.
        assert sum(not cross(*bs) for bs in blocks_l) == 5
        assert sum(not cross(*bs) for bs in blocks_r) == 5
        rows.append(dict(left=left, right=right, crossing=crossing,
                         compatible_pairs=sorted(relation),
                         cover=covers[0] if covers else None))
    result = dict(status='VERIFIED-COMP', interleavings=len(rows),
                  crossing_interleavings=sum(r['crossing'] for r in rows),
                  nonempty_crossing_relations=sum(r['crossing'] and bool(r['compatible_pairs']) for r in rows),
                  majority_triples_checked=triples,
                  all_ten_pair_choices=PAIRS, rows=rows)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('rows', 'all_ten_pair_choices')}))


if __name__ == '__main__':
    main()
