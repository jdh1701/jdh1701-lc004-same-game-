"""Exhaustive disjoint dihedral orbit cover of the unique six-point class."""
from pathlib import Path
from itertools import combinations
from math import comb
import json
HERE=Path(__file__).resolve().parent
unseen={sum(1<<i for i in c) for c in combinations(range(21),6)}
rows=[]
while unseen:
    m=min(unseen);positions=[i for i in range(21) if m>>i&1]
    orbit={sum(1<<((s*i+t)%21) for i in positions) for s in (1,-1) for t in range(21)}
    assert orbit<=unseen
    rows.append((m,len(orbit)));unseen-=orbit
assert sum(w for _,w in rows)==comb(21,6)
(HERE/'six_orbits.txt').write_text(''.join(f'{m} {w}\n' for m,w in rows))
out=dict(n=21,orbits=len(rows),weight_sum=sum(w for _,w in rows),all_patterns=comb(21,6)*126126)
(HERE/'preparation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
