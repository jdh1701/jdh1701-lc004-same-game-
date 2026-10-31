"""Derive the gap replacement map from original blocks; independently check
all 280 actual interleavings and the 3/4-generator signed join kernels.
No finite check is promoted to an all-length geometric classification.
"""
from pathlib import Path
from itertools import combinations
import sys,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import catalogue,blocks,crossing,join,join_value
C5=catalogue(5);C6=catalogue(6)
def avoids(c,g,h,offset):
    return not any(crossing(tuple(2*i for i in B),(2*g+offset,2*h+offset)) for B in blocks(c))
old=[[avoids(c,g,h,3) for g in range(4) for h in range(4)] for c in C5]
new=[[avoids(c,g,h,5) for g in range(4) for h in range(4)] for c in C6]
lift=[2,3,2,3,1,0,1,4] # Python catalogue ordering; state4 has universal signature
assert all(new[s]==old[lift[s]] for s in range(8))
assert old[1]==old[4] and all(not old[1][i] or all(row[i] for row in old) for i in range(16))
interleavings=0
def compat(g,c,h,d):
    return not any(crossing(tuple(g[i] for i in x),tuple(h[i] for i in y)) for x in blocks(c) for y in blocks(d))
for tail in combinations(range(3,11),3):
    A=(0,1,2)+tail;B=tuple(i for i in range(11) if i not in A)
    a=tuple(i-(i>1) for i in A if i!=1);b=tuple(i-1 for i in B)
    for cb in C5:
        before=[compat(a,c,b,cb) for c in C5];after=[compat(A,c,B,cb) for c in C6]
        assert all(after[s]==before[lift[s]] for s in range(8));interleavings+=1
        assert not before[1] or all(before)
        assert not before[4] or all(before)
def norm(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
rows=[]
for a,b in combinations((0,2,3),2):
    cs=[];states=[]
    for s in range(8):
        if lift[s] not in (a,b):continue
        outside=C5[0 if lift[s]==a else 1]
        cs.append(norm(tuple(C6[s])+tuple(6+x for x in outside)));states.append(s)
    p=(0,)*6+(1,)*5
    edges=[(i,j) for i,j in combinations(range(len(cs)),2) if join(cs[i],cs[j])==p]
    val=join_value(tuple(cs),p);expected=-1 if 0 in (a,b) else 1
    assert val==expected and len(cs)==(3 if expected==-1 else 4)
    assert len(edges)==2
    rows.append(dict(python_old_states=[a,b],python_new_states=states,synthetic_generators=cs,top_join_pairs=edges,coefficient=val,realizability='not asserted'))
out=dict(status='VERIFIED-COMP',gap_pairs=16,local_states=13,actual_interleavings=interleavings,python_lift_map=lift,lean_lift_map=[2,4,0,1,0,3,1,4],rows=rows,scope='Exact local replacement identities and abstract signed-join kernels. Positive kernel does not exhibit an actual connected first-excess game pattern.')
(HERE/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
