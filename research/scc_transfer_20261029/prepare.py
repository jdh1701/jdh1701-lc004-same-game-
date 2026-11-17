"""Finite local table conversion and exhaustive first-block orbit certificates."""
import itertools,json,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
FOLDER=Path(__file__).parent
rows=json.loads((ROOT/'research/five_geometry_20261029/ten_split_check.json').read_text())['rows']
valid=[0,3,4,7,9];lookup={x:i for i,x in enumerate(valid)}
table=[(0,0)]*1024
for row in rows:
    m=sum(1<<i for i in row['left'])
    rel=sum(1<<(lookup[x]*5+lookup[y]) for x,y in row['compatible_pairs'])
    table[m]=(rel,int(row['crossing']))
(FOLDER/'geometry5.txt').write_text(''.join(f'{r} {c}\n' for r,c in table))
for n in (20,25):
    unseen={sum(1<<i for i in p) for p in itertools.combinations(range(n),5)}
    orbits=[]
    while unseen:
        m=min(unseen);positions=[i for i in range(n) if m>>i&1]
        orbit={sum(1<<((s*i+t)%n) for i in positions) for s in (1,-1) for t in range(n)}
        assert orbit<=unseen
        orbits.append((m,len(orbit)));unseen-=orbit
    assert sum(w for _,w in orbits)==math.comb(n,5)
    assert len(orbits)=={20:406,25:1096}[n]
    (FOLDER/f'first_block_orbits_{n}.txt').write_text(''.join(f'{m} {w}\n' for m,w in orbits))
    result=dict(status='VERIFIED-COMP',n=n,local_interleavings=len(rows),first_block_orbits=len(orbits),total_five_subsets=math.comb(n,5),weight_sum=sum(w for _,w in orbits))
    (FOLDER/f'preparation_{n}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
