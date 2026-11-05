"""Position-partition join replay of the original five-class coefficient bridge.

No SCC, compatibility tables, or compressed join states are used by the join
calculation. Finite validation only; the general result is proved in Lean.
"""
import collections
import itertools as it
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'research'))
from certificate_join_count import canonical, join


def crossing(a, b):
    return any(x < u < y < v or u < x < v < y
               for x, y in it.combinations(a, 2)
               for u, v in it.combinations(b, 2))


def connected(groups):
    seen = {0}
    while True:
        more = {j for i in seen for j in range(len(groups))
                if crossing(groups[i], groups[j])}
        if more <= seen:
            return len(seen) == len(groups)
        seen |= more


def original_certificates(groups):
    n = sum(map(len, groups))
    choices = [[(pair, tuple(x for x in g if x not in pair))
                for pair in it.combinations(g, 2)] for g in groups]
    certs = []
    for split in it.product(*choices):
        blocks = sum((list(s) for s in split), [])
        if all(not crossing(a, b) for a, b in it.combinations(blocks, 2)):
            certs.append(canonical(blocks, n))
    assert len(certs) == len(set(certs)), 'duplicate original generator'
    return certs


def collected_coefficient(certs, p):
    weights = {}
    for c in certs:
        delta = collections.Counter({c: 1})
        for q, weight in weights.items():
            delta[join(q, c)] -= weight
        for q, weight in delta.items():
            weights[q] = weights.get(q, 0) + weight
            if weights[q] == 0:
                del weights[q]
    return weights.get(p, 0)


def check(groups):
    groups = tuple(tuple(sorted(g)) for g in groups)
    p = canonical(groups, sum(map(len, groups)))
    certs = original_certificates(groups)
    value = collected_coefficient(certs, p)
    if len(groups) >= 2 and connected(groups):
        predicted = -int(len(certs) == 2 and join(*certs) == p)
        assert value == predicted, (groups, value, predicted)
        if len(certs) >= 3:
            assert value == 0
    return value, len(certs), connected(groups)


def main():
    rows = []
    # Every unlabeled partition of ten positions into two five-point classes.
    for tail in it.combinations(range(1, 10), 4):
        g = (0,) + tail
        h = tuple(x for x in range(10) if x not in g)
        rows.append(check((g, h)))
    assert len(rows) == 126
    assert sum(v == -1 for v, _, c in rows if c) == 5
    # Existing fixtures include rejected SCC candidates with third certificates.
    fixtures = json.loads((ROOT / 'research/five_actual_20261029/implication_fixtures.json').read_text())
    for f in fixtures:
        rows.append(check(f['groups']))
    rng = random.Random(20261029)
    for k in (2, 3, 4, 5):
        for _ in range(40):
            positions = list(range(5*k))
            rng.shuffle(positions)
            rows.append(check([positions[5*i:5*i+5] for i in range(k)]))
    # Boundary and necessity controls, asserted separately from connected law.
    singleton = check((tuple(range(5)),))
    disconnected = check((tuple(range(5)), tuple(range(5, 10))))
    assert singleton[:2] == (-4, 5)
    assert disconnected[:2] == (16, 25) and not disconnected[2]
    result = dict(status='VERIFIED-COMP', original_position_join_cases=len(rows),
                  connected_cases=sum(c for _, _, c in rows),
                  connected_histogram=dict(collections.Counter(str(v) for v, _, c in rows if c)),
                  original_generator_count_histogram=dict(collections.Counter(str(n) for _, n, _ in rows)),
                  exhaustive_n10_partitions=126, existing_fixtures=len(fixtures),
                  random_cases=160, seed=20261029,
                  singleton_coefficient=singleton[0], disconnected_coefficient=disconnected[0],
                  failures=0)
    Path(__file__).with_name('original_bridge_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
