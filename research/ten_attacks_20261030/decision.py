"""Attack10: exact deletion/link decision recurrence, plus elementary collapses."""
from core import *
import json,collections,time
HERE=Path(__file__).resolve().parent

def key(fs):return tuple(sorted(tuple(sorted(f)) for f in maximal(fs)))
@lru_cache(None)
def decision(fs):
    if not fs:return 0
    if fs==((),):return 1
    vs=set().union(*map(set,fs));fsets=list(map(set,fs))
    if set.intersection(*fsets):return 0
    # Balanced incidence is a deterministic branching rule, not a correctness assumption.
    v=min(vs,key=lambda v:(abs(2*sum(v in f for f in fsets)-len(fsets)),v))
    delete=key(f-{v} for f in fsets)
    link=key(f-{v} for f in fsets if v in f)
    return decision(delete)-decision(link)

def elementary(F):
    F=set(F);steps=[]
    while True:
        pair=None
        # A codimension-one face in exactly one maximal face is elementary-free.
        maxs=maximal(F)
        for f in sorted(maxs,key=lambda s:(-len(s),sorted(s))):
            if len(f)<2:continue
            for v in sorted(f):
                g=f-{v}
                if sum(g<=h for h in maxs)==1:pair=(g,f);break
            if pair:break
        if pair is None:break
        g,f=pair
        assert g in F and f in F and len(f)==len(g)+1
        assert {h for h in F if g<=h}=={g,f}
        F.remove(g);F.remove(f);steps.append([sorted(g),sorted(f)])
    return F,steps

T=json.loads((HERE/'topology.json').read_text())['rows']
H=json.loads((HERE/'holdout.json').read_text())['rows']
checks=[];start=time.time()
for r in T+H:
    p=tuple(r['p']);cs,fs,_=generators(p)
    before=decision.cache_info().misses
    value=decision(key(fs));assert value==r['coefficient'],r
    checks.append(dict(p=p,new_nodes=decision.cache_info().misses-before,value=value))
    # memory stays bounded by small facet families, not all faces
residuals=[]
for r in H:
    if r['coefficient'] or r['remaining_vertices']==1:continue
    _,fs,_=generators(tuple(r['p']));red,strong=strong_collapse(fs)
    F=faces(red);remaining,steps=elementary(F)
    assert sum((-1)**len(f) for f in F)==sum((-1)**len(f) for f in remaining)
    residuals.append(dict(p=r['p'],strong_steps=strong,elementary_steps=steps,remaining=[sorted(f) for f in remaining],remaining_vertices=len(set().union(*remaining)),initial_faces=len(F)))
out=dict(status='VERIFIED-COMP',checks=len(checks),decision_nodes=decision.cache_info().misses,max_new_nodes=max(r['new_nodes'] for r in checks),rows=checks,
    stalled_strong_collapses=len(residuals),elementary_collapsed_to_point=sum(r['remaining_vertices']==1 for r in residuals),residuals=residuals,seconds=time.time()-start)
(HERE/'decision.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('rows','residuals')},indent=2),flush=True)
