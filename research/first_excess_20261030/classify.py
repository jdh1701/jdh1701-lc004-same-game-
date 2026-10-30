"""Replay complete local families and record the two surviving join shapes."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import sys,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import generators,blocks,join,join_value
def canon(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
def orbit(p):return min(canon(q[t:]+q[:t]) for q in (p,p[::-1]) for t in range(16))
shapes=Counter();orbits={};rows=[]
for line in (HERE/'nonzero.txt').read_text().splitlines():
    a,b,c,value,count=map(int,line.split());p=canon(next(j for j,g in enumerate((a,b,c)) if g>>i&1) for i in range(16))
    cs,_,_=generators(p);assert len(cs)==count and join_value(cs,p)==value==-1
    edges=[(i,j) for i,j in combinations(range(count),2) if join(cs[i],cs[j])==p]
    assert len(edges)=={2:1,3:2}[count]
    six=next(g for g in blocks(p) if len(g)==6)
    types=sorted(tuple(sorted(len(B) for B in blocks(q) if B[0] in six)) for q in cs)
    shapes[(count,str(types))]+=1
    key=orbit(p);orbits.setdefault(key,[]).append(p)
    rows.append(dict(p=p,generators=cs,top_join_pairs=edges,six_class_certificate_types=types))
representatives=[]
for p,members in sorted(orbits.items()):
    r=next(r for r in rows if tuple(r['p'])==p)
    representatives.append(dict(r,orbit_size=len(members)))
out=dict(status='VERIFIED-COMP',patterns=len(rows),join_shape_histogram={str(k):v for k,v in shapes.items()},dihedral_representatives=representatives)
(HERE/'classification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='dihedral_representatives'}))
