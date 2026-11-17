"""Test whether first-excess survivors reduce to all-five survivors.
This is a falsification/finite classification probe, not a general theorem.
"""
from pathlib import Path
from collections import Counter
import sys,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler

def word(gs):return tuple(next(j for j,g in enumerate(gs) if g>>i&1) for i in range(16))
def norm(w):
    d={};return tuple(d.setdefault(c,len(d)) for c in w)
def connected(w):
    groups=[{i for i,c in enumerate(w) if c==a} for a in set(w)]
    def cross(a,b):
        s=[c for _,c in sorted([(i,0) for i in a]+[(i,1) for i in b])]
        return sum(i==0 or s[i]!=s[i-1] for i in range(len(s)))>=4
    while len(groups)>1:
        pair=next(((i,j) for i in range(len(groups)) for j in range(i) if cross(groups[i],groups[j])),None)
        if pair is None:return False
        i,j=pair;groups[j]|=groups.pop(i)
    return True

cache={};rows=[];orbits={};cyclic={};types=Counter()
for line in (HERE/'nonzero.txt').read_text().splitlines():
    a,b,c,value,generators=map(int,line.split());p=word((a,b,c));reductions=[];adjacent=[]
    for i in range(16):
        if p[i]!=2:continue
        q=norm(p[:i]+p[i+1:])
        if q not in cache:
            d=encode(q);cache[q]=(connected(q),euler(d['facets']) if d['generators'] else 0)
        hc,v=cache[q]
        if hc and v==-1:
            reductions.append(i)
            if p[(i-1)%16]==2 or p[(i+1)%16]==2:adjacent.append(i)
    cp=min(norm(p[t:]+p[:t]) for t in range(16));dp=min(norm(q[t:]+q[:t]) for q in (p,p[::-1]) for t in range(16))
    cyclic.setdefault(cp,[]).append(p);orbits.setdefault(dp,[]).append(p)
    types[(generators,len(reductions),len(adjacent))]+=1
    rows.append(dict(p=p,generators=generators,all_five_deletions=reductions,adjacent_all_five_deletions=adjacent))
out=dict(status='VERIFIED-COMP',patterns=len(rows),cyclic_orbits=len(cyclic),dihedral_orbits=len(orbits),cyclic_orbit_sizes=dict(Counter(map(len,cyclic.values()))),dihedral_orbit_sizes=dict(Counter(map(len,orbits.values()))),without_all_five_reduction=[r for r in rows if not r['all_five_deletions']],without_adjacent_reduction=[r for r in rows if not r['adjacent_all_five_deletions']],deletion_histogram={str(k):v for k,v in types.items()},rows=rows)
(HERE/'reductions.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v if not isinstance(v,list) else len(v) for k,v in out.items() if k!='rows'}),flush=True)
