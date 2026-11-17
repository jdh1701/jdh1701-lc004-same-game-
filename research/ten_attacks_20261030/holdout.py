"""Predeclared holdout for the strong-collapse and low-dimensional homology leads."""
from core import *
import random,json,collections,time
HERE=Path(__file__).resolve().parent
rng=random.Random(20261030);start=time.time();rows=[];certificates=[];fail=[]
def connected(p):
    gs=blocks(p);seen={0}
    while True:
        new=seen|{j for i in seen for j in range(len(gs)) if crossing(gs[i],gs[j])}
        if new==seen:return len(seen)==len(gs)
        seen=new

def sample(profile,count):
    pool=sum(([a]*n for a,n in enumerate(profile)),[]);seen=set()
    while len(seen)<count:
        rng.shuffle(pool);names={};p=tuple(names.setdefault(a,len(names)) for a in pool)
        if p not in seen:seen.add(p);yield p

for profile,pats in [((6,7),two_patterns(6,7)),((7,7),two_patterns(7,7)),((5,5,6),sample((5,5,6),300)),((5,6,7),sample((5,6,7),300)),((8,8),sample((8,8),100))]:
    for p in pats:
        if not connected(p):continue
        cs,fs,choices=generators(p)
        if full_join(cs,len(p))!=p:continue
        F=faces(fs);val=sum((-1)**len(f) for f in F)
        reduced,steps=strong_collapse(fs);rf=faces(reduced)
        assert sum((-1)**len(f) for f in rf)==val
        nv=len(set().union(*reduced)) if reduced else 0
        # Cap independent join-DP by generator count; include every such case.
        if len(cs)<=16:assert join_value(cs,p)==val
        hom=homology_f2(rf) if len(rf)<30000 else None
        r=dict(profile=profile,p=p,generators=len(cs),coefficient=val,faces=len(F),remaining_vertices=nv,remaining_faces=len(rf),homology=hom)
        rows.append(r)
        if val==0 and nv!=1:fail.append(r)
        certificates.append(dict(p=p,steps=steps,remaining=[sorted(f) for f in reduced]))
    print(profile,'full-join rows',len(rows),'counterexamples',len(fail),'seconds',time.time()-start,flush=True)
out=dict(status='VERIFIED-COMP',seed=20261030,rows=rows,zero_collapse_counterexamples=fail,seconds=time.time()-start)
(HERE/'holdout.json').write_text(json.dumps(out,indent=2)+'\n')
(HERE/'holdout_collapses.json').write_text(json.dumps(certificates,indent=2)+'\n')
print('histogram',collections.Counter((tuple(r['profile']),r['coefficient'],r['remaining_vertices']) for r in rows),flush=True)
