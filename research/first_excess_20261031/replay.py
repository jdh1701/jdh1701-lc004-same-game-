"""Independent Euler replay of every full-join orbit candidate; original joins
for every positive representative. This is not an independent full census.
"""
from pathlib import Path
from collections import Counter
import sys,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler
from core import generators,join_value
def norm(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
def word(ms,n):return norm(next(j for j,m in enumerate(ms) if m>>i&1) for i in range(n))
def orbit(p):return {norm(q[t:]+q[:t]) for q in (p,p[::-1]) for t in range(len(p))}
def runs(p,a):
    starts=[i for i in range(len(p)) if p[i]!=p[(i-1)%len(p)]]
    return tuple(sorted((starts[(k+1)%len(starts)]-i)%len(p) for k,i in enumerate(starts) if p[i]==a))
def connected(p):
    gs=[{i for i,c in enumerate(p) if c==a} for a in set(p)]
    def cross(A,B):
        w=[c for _,c in sorted([(i,0) for i in A]+[(i,1) for i in B])]
        return sum(i==0 or w[i]!=w[i-1] for i in range(len(w)))>=4
    while len(gs)>1:
        edge=next(((i,j) for i in range(len(gs)) for j in range(i) if cross(gs[i],gs[j])),None)
        if edge is None:return False
        i,j=edge;gs[j]|=gs.pop(i)
    return True
rows=[];expanded=set();hist=Counter();delhist=Counter();candidates=0
for line in (HERE/'full_join.txt').read_text().splitlines():
    a,b,c,six,weight,value,count=map(int,line.split());p=word((a,b,c,six),21)
    d=encode(p);assert d['generators']==count and d['full_join'] and connected(p)
    assert euler(d['facets'])==value
    candidates+=1
    if not value:continue
    cs,_,_=generators(p);assert len(cs)==count and join_value(cs,p)==value
    op=orbit(p);assert len(op)%weight==0;expanded|=op
    sixlabel=next(a for a in set(p) if p.count(a)==6)
    shape=runs(p,sixlabel)
    five_shapes=[runs(p,a) for a in set(p) if a!=sixlabel]
    deletions=[]
    for a in set(p)-{sixlabel}:
        q=norm(x for x in p if x!=a);e=encode(q)
        if connected(q) and euler(e['facets'])!=0:deletions.append(a)
    hist[str((count,shape,tuple(five_shapes)))]+=weight
    delhist[str((count,len(deletions)))]+=weight
    rows.append(dict(p=p,coefficient=value,generators=count,six_subset_orbit_weight=weight,pattern_orbit_size=len(op),six_runs=shape,five_runs=five_shapes,successful_class_deletions=deletions))
    if len(rows)%50==0:print('positive representatives',len(rows),flush=True)
assert len(expanded)==sum(r['six_subset_orbit_weight'] for r in rows)
out=dict(status='VERIFIED-COMP',scope='All full-join representatives replayed; independent positive signed joins; census completeness relies on the exhaustive C++ construction.',full_join_representatives=candidates,nonzero_representatives=len(rows),explicit_patterns=len(expanded),shape_histogram=dict(hist),class_deletion_histogram=dict(delhist),rows=rows,source_sha256=hashlib.sha256((HERE/'count.cpp').read_bytes()).hexdigest())
(HERE/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)
