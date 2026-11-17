# Independent Sage graph implementation and full small-family replay.
import json, itertools
from pathlib import Path
rows = json.loads(Path('research/five_actual_20261029/implication_fixtures.json').read_text())
counts = {2: 0, 3: 0}
for row in rows:
    k = len(row['groups'])
    a, b = tuple(row['a']), tuple(row['b'])
    constraints = {(r['i'],r['j']): set(map(tuple,r['pairs'])) for r in row['edges']}
    arcs = []
    for (i,j), rel in constraints.items():
        if (b[i],a[j]) not in rel: arcs.append((i,j))
        if (a[i],b[j]) not in rel: arcs.append((j,i))
    graph = DiGraph(multiedges=False, loops=False)
    graph.add_vertices(range(k))
    graph.add_edges(arcs)
    strong = graph.is_strongly_connected()
    assert strong == row['strong']
    sols = {x for x in itertools.product([0,3,4,7,9], repeat=k)
            if all((x[i],x[j]) in rel for (i,j),rel in constraints.items())}
    assert a in sols and b in sols and all(x != y for x,y in zip(a,b))
    assert strong == (sols == {a,b})
    if not strong:
        assert tuple(row["third"]) in sols - {a,b}
    counts[k] += int(strong)
assert len(rows) == 268 and counts == {2:5, 3:35}
print('VERIFIED-COMP: Sage SCC and full certificate replay agree on all 268 candidate graphs; counts 5,35')
