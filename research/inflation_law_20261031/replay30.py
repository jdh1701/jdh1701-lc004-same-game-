"""Independent replay of the first 64 positive n30 insertion completions.
Also check the inherited adjacent-pair property in all 767 input fixtures.
This does not independently replay every rejected completion.
"""
from pathlib import Path
from itertools import combinations
import sys,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler
def norm(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
pairRanks=[(0,1),(0,4),(1,2),(2,3),(3,4)]
fixture=ROOT/'research/scc_transfer_20261029/survivor_witnesses_25.txt'
checked=0
for line in fixture.read_text().splitlines():
    row=list(map(int,line.split()));masks=row[:5];a=row[5:10];b=row[10:]
    for k,m in enumerate(masks):
        g=[i for i in range(25) if m>>i&1]
        pairs=[{g[i] for i in pairRanks[s]} for s in (a[k],b[k])]
        for i in range(5):
            if (g[(i+1)%5]-g[i])%25==1:assert {g[i],g[(i+1)%5]} in pairs
    checked+=1
assert checked==767
positive=0
for line in (HERE/'counterexamples30.txt.sample').read_text().splitlines():
    masks=list(map(int,line.split()));assert len(masks)==6
    p=norm(next(j for j,m in enumerate(masks) if m>>i&1) for i in range(30))
    d=encode(p);assert d['generators']==2 and d['full_join'] and euler(d['facets'])==-1
    # Inserting points cannot create new adjacency between old positions.
    # Check all classes here nonetheless, in the independent Python ordering.
    from core import catalogue,blocks
    gs=blocks(p)
    for k,g in enumerate(gs):
        pairs=[]
        for cs in d['choices']:
            local=next(B for B in blocks(catalogue(5)[cs[k]]) if len(B)==2)
            pairs.append({g[i] for i in local})
        for i in range(5):
            if (g[(i+1)%5]-g[i])%30==1:assert {g[i],g[(i+1)%5]} in pairs
    positive+=1
assert positive==64
out=dict(status='VERIFIED-COMP',parent_adjacency_fixtures_checked=checked,positive_completions_independently_replayed=positive,fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),scope='All fixture adjacency properties; first 64 positive completions only. No independent exhaustive replay of the bounded search.')
(HERE/'replay30.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
