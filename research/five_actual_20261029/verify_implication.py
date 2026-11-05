"""Adversarial tests of the raw-constraint SCC survivor criterion.

Exact finite exhaustions and hypothesis-removal controls; not a general count.
The SCC graph never uses projections computed from the full solution family.
"""
import itertools as it
import json
from pathlib import Path


def majority(x, y, z):
    return y if y == z else x


def closed(r):
    return all((majority(a[0], b[0], c[0]), majority(a[1], b[1], c[1])) in r
               for a, b, c in it.product(r, repeat=3))


def covered(r, d):
    return any(all(x == p or y == q for x, y in r)
               for p, q in it.product(range(d), repeat=2))


def implication_reach(k, edges, a, b):
    reach = [{i} for i in range(k)]
    for (i, j), r in edges.items():
        if (b[i], a[j]) not in r:
            reach[i].add(j)
        if (a[i], b[j]) not in r:
            reach[j].add(i)
    for mid in range(k):
        for i in range(k):
            if mid in reach[i]:
                reach[i] |= reach[mid]
    return reach


def graph_strong(k, edges, a, b):
    return all(len(row) == k for row in implication_reach(k, edges, a, b))


def solve(k, d, edges):
    return [a for a in it.product(range(d), repeat=k)
            if all((a[i], a[j]) in r for (i, j), r in edges.items())]


def main():
    required = {(0, 0), (1, 1)}
    optional = sorted(set(it.product(range(3), repeat=2)) - required)
    relations = []
    for mask in range(1 << len(optional)):
        r = required | {p for t, p in enumerate(optional) if mask >> t & 1}
        if closed(r):
            relations.append(r)
    systems = 0
    rigid = 0
    for rs in it.product(relations, repeat=3):
        if not any(covered(r, 3) for r in rs):
            continue
        edges = dict(zip(((0, 1), (0, 2), (1, 2)), rs))
        a, b = (0, 0, 0), (1, 1, 1)
        sols = solve(3, 3, edges)
        criterion = graph_strong(3, edges, a, b)
        assert criterion == (set(sols) == {a, b}), (edges, sols)
        systems += 1
        rigid += criterion

    rows = json.loads((Path(__file__).parents[1] /
                       'five_geometry_20261029/ten_split_check.json').read_text())['rows']
    geom_pairs = 0
    geom_rigid = 0
    for row in rows:
        if not row['crossing']:
            continue
        r = set(map(tuple, row['compatible_pairs']))
        for a, b in it.combinations(sorted(r), 2):
            if any(x == y for x, y in zip(a, b)):
                continue
            actual = graph_strong(2, {(0, 1): r}, a, b)
            assert actual == (r == {a, b})
            geom_pairs += 1
            geom_rigid += actual

    # These controls refute shortcuts that omit material hypotheses.
    no_cover = {(0, 0), (1, 1), (2, 2)}
    assert closed(no_cover) and not covered(no_cover, 3)
    assert graph_strong(2, {(0, 1): no_cover}, (0, 0), (1, 1))
    assert len(no_cover) == 3
    no_closure = {(0, 0), (1, 1), (0, 2)}
    assert covered(no_closure, 3) and not closed(no_closure)
    assert graph_strong(2, {(0, 1): no_closure}, (0, 0), (1, 1))
    assert len(no_closure) == 3
    no_separation = {(0, 0), (0, 1)}
    assert closed(no_separation) and covered(no_separation, 2) and len(no_separation) == 2
    assert not graph_strong(2, {(0, 1): no_separation}, (0, 0), (0, 1))
    # A={000,111} with universal raw constraints violates the binary spec;
    # a graph formed from those raw constraints is not strongly connected.
    universal = set(it.product(range(2), repeat=2))
    assert len(solve(3, 2, {(i,j):universal for i,j in it.combinations(range(3),2)})) == 8
    assert not graph_strong(3, {(i, j): universal for i, j in it.combinations(range(3), 2)},
                            (0, 0, 0), (1, 1, 1))
    result = dict(status='VERIFIED-COMP', majority_closed_relations=len(relations),
                  exhaustive_three_variable_systems=systems, rigid_systems=rigid,
                  geometric_separated_pairs=geom_pairs, geometric_rigid_pairs=geom_rigid,
                  hypothesis_removal_controls=4, failures=0)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
