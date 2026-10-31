"""Independent endpoint/run certificate replay of every accepted n25 orbit case.
Does not use the C++ relation table or its SCC implementation.
"""
import json,sys,collections
from pathlib import Path
FOLDER=Path(__file__).resolve().parent
sys.path.insert(0,str(FOLDER.parents[0]/'choice_complex_20261029'))
import core
weights={int(m):int(w) for m,w in map(str.split,(FOLDER/'first_block_orbits_25.txt').read_text().splitlines())}
rows=[list(map(int,line.split())) for line in (FOLDER/'survivor_witnesses_25.txt').read_text().splitlines()]
seen=set();hist=collections.Counter()
for row in rows:
    assert len(row)==15
    masks=row[:5];a=tuple(row[5:10]);b=tuple(row[10:15])
    assert all(m.bit_count()==5 for m in masks)
    assert sum(masks)==(1<<25)-1 and sum(m.bit_count() for m in masks)==25
    assert not any(x&y for i,x in enumerate(masks) for y in masks[i+1:])
    key=(masks[0],tuple(sorted(masks[1:])))
    assert key not in seen;seen.add(key)
    groups=[tuple(i for i in range(25) if m>>i&1) for m in masks]
    assert core.connected(groups)
    choices,options=core.atoms(groups)
    assert len(choices)==2 and set(choices)=={a,b}
    assert all(x!=y for x,y in zip(a,b))
    assert core.coefficient(choices,5)[0]==-1
    hist[masks[0]]+=1
orbit_rows=[list(map(int,line.split())) for line in (FOLDER/'orbit_results_25.txt').read_text().splitlines()]
assert len(orbit_rows)==1096 and sum(w for _,w,_,_ in orbit_rows)==53130
assert all(hist[m]==hits for m,w,hits,candidates in orbit_rows)
weighted=sum(weights[m] for m,_ in seen)
assert weighted==32275 and weighted//5==6455
out=dict(status='VERIFIED-COMP',positive_marked_orbit_cases=len(rows),independent_full_family_replays=len(rows),weighted_survivors=weighted,survivors=weighted//5,failures=0)
(FOLDER/'witness_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
