"""Targeted falsification after mixed-degree homology was observed at(6,10).
Exhaust all positive six-run compositions of(6,10); budgets explicitly recorded.
"""
from core import *
import json,time,collections
HERE=Path(__file__).resolve().parent

def comps(n,k):
    if k==1:yield (n,);return
    for a in range(1,n-k+2):
        for rest in comps(n-a,k-1):yield (a,)+rest
rows=[];start=time.time();counterexamples=[]
for aa in comps(6,3):
    for bb in comps(10,3):
        p=tuple(c for i in range(3) for c in [0]*aa[i]+[1]*bb[i])
        cs,fs,_=generators(p)
        if full_join(cs,len(p))!=p:
            rows.append(dict(p=p,status='proper-generator-join'));continue
        if len(cs)>400:
            rows.append(dict(p=p,status='SKIPPED-generator-budget',generators=len(cs)));continue
        reduced,steps=strong_collapse(fs)
        upper=sum(1<<len(f) for f in reduced)
        if upper>300000:
            rows.append(dict(p=p,status='SKIPPED-face-budget',upper=upper));continue
        F=faces(reduced);val=sum((-1)**len(f) for f in F)
        if len(F)>3000:
            rows.append(dict(p=p,status='SKIPPED-homology-budget',coefficient=val,faces=len(F)));continue
        hom=homology_f2(F)
        r=dict(p=p,status='evaluated',generators=len(cs),coefficient=val,faces=len(F),homology=hom)
        rows.append(r)
        if val==0 and any(hom):counterexamples.append(r)
out=dict(status='VERIFIED-COMP',patterns=len(rows),rows=rows,zero_with_nonzero_homology=counterexamples,seconds=time.time()-start)
(HERE/'homology_search.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',len(rows),'statuses',collections.Counter(r['status'] for r in rows),'counterexamples',len(counterexamples),'seconds',time.time()-start,flush=True)
print(json.dumps(counterexamples[:2],indent=2),flush=True)
