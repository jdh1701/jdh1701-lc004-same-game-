"""Recompute known all-five support counts using two searches and SCC recognition.

No enumeration of the full certificate family or signed join expansion is used.
This is exact finite counting, not a general formula or a new count at n20/n25.
"""
import itertools as it
import json
from pathlib import Path
from verify_implication import implication_reach

ROOT = Path(__file__).resolve().parents[2]
TABLE = {tuple(r['left']): r for r in json.loads(
    (ROOT / 'research/five_geometry_20261029/ten_split_check.json').read_text())['rows']}
PAIRS = tuple(it.combinations(range(5), 2))


def cross(a, b):
    return any(u < x < v < y or x < u < y < v
               for u, v in it.combinations(sorted(a), 2)
               for x, y in it.combinations(sorted(b), 2))


VALID = tuple(s for s, pair in enumerate(PAIRS)
              if not cross(pair, tuple(i for i in range(5) if i not in pair)))
assert len(VALID) == 5


def partitions(remaining, groups):
    if groups == 1:
        yield (remaining,)
        return
    first, *tail = remaining
    for others in it.combinations(tail, 4):
        block = (first,) + others
        chosen = set(block)
        rest = tuple(x for x in remaining if x not in chosen)
        for suffix in partitions(rest, groups - 1):
            yield (block,) + suffix


def count(k, fixtures):
    result = dict(classes=k, positions=5*k, patterns=0, connected=0,
                  feasible=0, separated_pair_found=0, support=0, search_nodes=0)
    for groups in partitions(tuple(range(5*k)), k):
        result['patterns'] += 1
        edges = {}
        crossing_edges = [set() for _ in range(k)]
        impossible = False
        for i, j in it.combinations(range(k), 2):
            union = sorted(groups[i] + groups[j])
            ranks = {v: t for t, v in enumerate(union)}
            row = TABLE[tuple(ranks[v] for v in groups[i])]
            edges[i, j] = set(map(tuple, row['compatible_pairs']))
            if not edges[i, j]:
                impossible = True
            if row['crossing']:
                crossing_edges[i].add(j)
                crossing_edges[j].add(i)
        seen, pending = {0}, [0]
        while pending:
            v = pending.pop()
            for w in crossing_edges[v] - seen:
                seen.add(w)
                pending.append(w)
        if len(seen) != k:
            continue
        result['connected'] += 1
        if impossible:
            continue

        def find(forbidden=None):
            partial = []

            def rec():
                i = len(partial)
                if i == k:
                    return tuple(partial)
                for x in VALID:
                    if forbidden is not None and x == forbidden[i]:
                        continue
                    result['search_nodes'] += 1
                    if all((partial[j], x) in edges[j, i] for j in range(i)):
                        partial.append(x)
                        answer = rec()
                        partial.pop()
                        if answer is not None:
                            return answer
                return None
            return rec()

        a = find()
        if a is None:
            continue
        result['feasible'] += 1
        b = find(a)
        if b is None:
            continue
        result['separated_pair_found'] += 1
        reach = implication_reach(k, edges, a, b)
        strong = all(len(row) == k for row in reach)
        third = None
        if not strong:
            root = next(i for i in range(k) if len(reach[i]) < k)
            third = tuple(b[i] if i in reach[root] else a[i] for i in range(k))
            assert third != a and third != b
            assert all((third[i],third[j]) in rel for (i,j),rel in edges.items())
        fixtures.append(dict(groups=groups, a=a, b=b, third=third, strong=strong,
                             edges=[dict(i=i,j=j,pairs=sorted(r)) for (i,j),r in edges.items()]))
        if strong:
            result['support'] += 1
    return result


if __name__ == '__main__':
    fixtures = []
    rows = [count(2, fixtures), count(3, fixtures)]
    Path(__file__).with_name("implication_fixtures.json").write_text(json.dumps(fixtures, separators=(",", ":")) + "\n")
    assert rows[0]['patterns'] == 126 and rows[0]['support'] == 5
    assert rows[1]['patterns'] == 126126 and rows[1]['support'] == 35
    result = dict(status='VERIFIED-COMP', method='first solution, separated second solution, raw-constraint SCC', rows=rows)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
