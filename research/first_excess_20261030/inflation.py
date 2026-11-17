"""Exact inflation-family verification; no claim that all first-excess cases arise.

Inputs: all five n10 parents, all 35 n15 parents recovered from the 556 census,
and the prior exhaustive n25 survivor orbit fixtures. Complete local original
certificate families are regenerated for every distinct tested inflation.
"""
from pathlib import Path
from collections import Counter
import json,sys,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler
from core import two_patterns
def norm(w):
    d={};return tuple(d.setdefault(c,len(d)) for c in w)
def runs(p):
    starts=[i for i in range(len(p)) if p[i]!=p[(i-1)%len(p)]]
    return [(i,(starts[(k+1)%len(starts)]-i)%len(p)) for k,i in enumerate(starts)]
def orbit(p):return {norm(q[t:]+q[:t]) for q in (p,p[::-1]) for t in range(len(p))}
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
red=json.loads((HERE/'reductions.json').read_text())['rows'];parents15=set()
parents10=set()
for p in two_patterns(5,5):
    d=encode(p)
    if d['generators'] and euler(d['facets'])==-1:parents10.add(p)
assert len(parents10)==5
for r in red:
    p=r['p']
    for i in r['all_five_deletions']:parents15.add(norm(p[:i]+p[i+1:]))
assert len(parents15)==35
source=ROOT/'research/scc_transfer_20261029/survivor_witnesses_25.txt'
parents25=set()
for line in source.read_text().splitlines():
    masks=list(map(int,line.split()))[:5]
    parents25.add(norm(next(j for j,m in enumerate(masks) if m>>i&1) for i in range(25)))
results=[]
for j,representatives,expected_sources,expected_children in [(2,parents10,5,22),(3,parents15,35,224),(5,parents25,6455,67132)]:
    allparents=set();tested=set();children=set();genhist=Counter()
    for p in sorted(representatives):
        for c in set(p):assert sorted(size for i,size in runs(p) if p[i]==c)==[1,2,2]
        d=encode(p);assert connected(p) and d['generators']==2 and euler(d['facets'])==-1
        allparents.update(orbit(p))
        for i,size in runs(p):
            if size!=2:continue
            q=norm(p[:i]+(p[i],)+p[i:])
            if q in tested:continue
            tested.add(q);d=encode(q);value=euler(d['facets'])
            assert connected(q) and d['generators']==3 and value==-1
            assert sum(size==3 for _,size in runs(q))==1
            genhist[(d['generators'],value)]+=1;children.update(orbit(q))
    assert len(allparents)==expected_sources and len(children)==expected_children
    assert 5*len(children)==2*(5*j+1)*len(allparents)
    if j==3:
        expected={norm(r['p']) for r in red if r['generators']==3}
        assert children==expected
    row=dict(j=j,parent_representatives=len(representatives),parent_patterns=len(allparents),distinct_inflations_replayed=len(tested),inflated_patterns=len(children),coefficient=-1,generators=3,count_formula_verified=True)
    results.append(row);print(json.dumps(row),flush=True)
out=dict(status='VERIFIED-COMP',source_fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),rows=results,scope='Complete inflation images of the certified n10, n15 and n25 all-five survivor families; NOT a complete n26 first-excess census or universal preservation theorem.')
(HERE/'inflation.json').write_text(json.dumps(out,indent=2)+'\n')
