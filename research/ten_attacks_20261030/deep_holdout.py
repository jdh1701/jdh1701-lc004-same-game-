"""Adversarial follow-up: inflated three-class fixtures and larger two-class runs.
Chosen after the first holdout. This is a new test, not an untouched holdout.
"""
from core import *
import random,json,time,collections
HERE=Path(__file__).resolve().parent
rng=random.Random(903017);start=time.time();patterns=set()
fixtures=json.loads((ROOT/'research/five_actual_20261029/implication_fixtures.json').read_text())
for f in fixtures:
    if len(f['groups'])!=3:continue
    p=canonical(tuple(tuple(g) for g in f['groups']),15)
    # All positions: one extra occurrence converts one class from five to six.
    for i in range(15):patterns.add(p[:i]+(p[i],)+p[i:])

def compose(n,k):
    cuts=sorted(rng.sample(range(1,n),k-1));return [b-a for a,b in zip([0]+cuts,cuts+[n])]
for a,b in [(8,9),(9,9),(6,10),(5,10)]:
    for runs in (2,3,4):
        for _ in range(15):
            aa=compose(a,runs);bb=compose(b,runs)
            patterns.add(tuple(c for i in range(runs) for c in [0]*aa[i]+[1]*bb[i]))

# Elementary collapse on a reduced complex; every removed pair is checked.
def elementary(F):
    F=set(F);steps=[]
    while True:
        maxs=maximal(F);pair=None
        for f in sorted(maxs,key=lambda s:(-len(s),sorted(s))):
            if len(f)<2:continue
            for v in sorted(f):
                g=f-{v}
                if sum(g<=h for h in maxs)==1:pair=g,f;break
            if pair:break
        if pair is None:break
        g,f=pair;assert {h for h in F if g<=h}=={g,f}
        F.remove(g);F.remove(f);steps.append([sorted(g),sorted(f)])
    return F,steps

rows=[];exceptions=[];traces=[]
print('Predeclared patterns',len(patterns),'generator cap400; face upper cap300000; elementary cap400; homology cap2000',flush=True)
for index,p in enumerate(sorted(patterns)):
    cs,fs,_=generators(p)
    if full_join(cs,len(p))!=p:continue
    if len(cs)>400:
        rows.append(dict(p=p,profile=list(map(len,blocks(p))),generators=len(cs),status="SKIPPED-generator-budget"));continue
    red,steps=strong_collapse(fs)
    nv=len(set().union(*red)) if red else 0
    # Bound face construction before allocating it; skip is recorded, not zero.
    upper=sum(1<<len(f) for f in red)
    if upper>300000:
        rows.append(dict(p=p,profile=list(map(len,blocks(p))),generators=len(cs),status='SKIPPED-face-budget',upper=upper));continue
    F=faces(red);val=sum((-1)**len(f) for f in F)
    rem,element=elementary(F) if val==0 and nv!=1 and len(F)<=400 else (F,[])
    r=dict(p=p,profile=list(map(len,blocks(p))),generators=len(cs),coefficient=val,remaining_vertices=len(set().union(*rem)) if rem else 0,strong_vertices=nv,faces=len(F),homology=homology_f2(rem) if len(rem)<=2000 else None)
    if val==0 and r['remaining_vertices']!=1:exceptions.append(r)
    rows.append(r);traces.append(dict(p=p,strong_steps=steps,elementary_steps=element,remaining=[sorted(f) for f in rem]))
    if len(rows)%50==0:print(index,'of',len(patterns),'full-join',len(rows),'seconds',time.time()-start,flush=True)
out=dict(status='VERIFIED-COMP',seed=903017,attempted_patterns=len(patterns),full_join_patterns=len(rows),rows=rows,zero_collapse_failures=exceptions,seconds=time.time()-start)
(HERE/'deep_holdout.json').write_text(json.dumps(out,indent=2)+'\n')
(HERE/'deep_traces.json').write_text(json.dumps(traces,indent=2)+'\n')
print('DONE',len(patterns),len(rows),'failures',len(exceptions),'hist',collections.Counter((tuple(sorted(r['profile'])),r.get('coefficient'),r.get('remaining_vertices')) for r in rows),'seconds',time.time()-start,flush=True)
