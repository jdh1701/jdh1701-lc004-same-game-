"""Construct ORIGINAL noncrossing certificates by recursive intervals.

Independent of the ten-split tables, SCC recognition, and the other replay's
classwise generator. Also compute signed joins of actual position partitions.
"""
from functools import lru_cache
from itertools import combinations, product
from collections import defaultdict, Counter
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'research/five_actual_20261029'))
from count_by_implication import partitions


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for i in range(n + 1):
            for tail in compositions(n - i, k - 1):
                yield (i,) + tail


@lru_cache(None)
def nc_certificates(pairs, triples):
    if pairs == triples == 0:
        return ((),)
    out = []
    for size in (2, 3):
        p, t = pairs - (size == 2), triples - (size == 3)
        if min(p, t) < 0:
            continue
        for ps in compositions(p, size):
            for ts in compositions(t, size):
                starts, roots, pos = [], [], 0
                for a, b in zip(ps, ts):
                    roots.append(pos)
                    starts.append(pos + 1)
                    pos += 1 + 2*a + 3*b
                for pieces in product(*(nc_certificates(a, b) for a, b in zip(ps, ts))):
                    blocks = [tuple(roots)]
                    for start, piece in zip(starts, pieces):
                        blocks.extend(tuple(start + x for x in block) for block in piece)
                    out.append(tuple(sorted(blocks)))
    assert len(out) == len(set(out))
    return tuple(out)


def crossing(A, B):
    return any(a < b < c < d or b < a < d < c
               for a, c in combinations(A, 2) for b, d in combinations(B, 2))


def classwise_certificates(groups):
    options = [[(pair, tuple(x for x in group if x not in pair))
                for pair in combinations(group, 2)] for group in groups]
    result = set()
    for choice in product(*options):
        blocks = tuple(sorted(block for split in choice for block in split))
        if not any(crossing(a, b) for a, b in combinations(blocks, 2)):
            result.add(blocks)
    return result


def labels(n, blocks):
    out = [None] * n
    for block in blocks:
        for x in block:
            assert out[x] is None
            out[x] = min(block)
    assert all(x is not None for x in out)
    return tuple(out)


def join(a, b):
    parent = list(range(len(a)))
    def find(x):
        while x != parent[x]:
            x = parent[x]
        return x
    for r in (a, b):
        for i, x in enumerate(r):
            u, v = find(i), find(x)
            parent[max(u, v)] = min(u, v)
    return tuple(find(i) for i in range(len(a)))


def original_coefficient(n, certificates, target):
    acc = {}
    for blocks in certificates:
        c = labels(n, blocks)
        nxt = defaultdict(int, acc)
        nxt[c] += 1
        for old, value in acc.items():
            nxt[join(old, c)] -= value
        acc = {r: v for r, v in nxt.items() if v}
    return acc.get(target, 0)


def raw_connected(groups):
    seen, todo = {0}, [0]
    while todo:
        i = todo.pop()
        for j in range(len(groups)):
            if j not in seen and crossing(groups[i], groups[j]):
                seen.add(j)
                todo.append(j)
    return len(seen) == len(groups)


def main():
    fixtures = json.loads((ROOT / 'research/five_actual_20261029/implication_fixtures.json').read_text())
    cases = {tuple(tuple(g) for g in f['groups']) for f in fixtures}
    cases.update(partitions(tuple(range(10)), 2))
    cases.add((tuple(range(5)),))
    counts, coefficients = Counter(), Counter()
    for groups in sorted(cases):
        k, n = len(groups), sum(map(len, groups))
        target = labels(n, groups)
        direct = {cert for cert in nc_certificates(k, k)
                  if all(len({target[x] for x in B}) == 1 for B in cert)}
        assert direct == classwise_certificates(groups), groups
        counts[f'n{n}_bijections'] += 1
        if k >= 2 and raw_connected(groups):
            coeff = original_coefficient(n, sorted(direct), target)
            witness = len(direct) == 2 and join(*(labels(n, c) for c in sorted(direct))) == target
            assert coeff == (-1 if witness else 0), (groups, coeff, len(direct))
            counts[f'n{n}_connected_coefficients'] += 1
            coefficients[str(coeff)] += 1
        if k == 1:
            assert len(direct) == 5
            assert original_coefficient(n, sorted(direct), target) == -4
            counts['single_class_exclusion_control'] += 1
    result = dict(status='VERIFIED-COMP', cases=dict(counts), coefficient_histogram=dict(coefficients),
                  global_nc_certificate_catalogue={f'n{5*k}':len(nc_certificates(k,k)) for k in (1,2,3)},
                  scope='n10 all 126 partitions; n15 saved separated-pair fixtures; n5 exclusion control',
                  method='global NC interval decomposition; actual position-partition signed joins')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
