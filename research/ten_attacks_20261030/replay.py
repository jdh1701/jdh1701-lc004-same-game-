"""Independent replay of structural certificates.
No import of core.py, search heuristics, signed coefficient tables or collapse code.
Local catalogues are enumerated as unrestricted set partitions and then filtered.
"""
from pathlib import Path
from functools import lru_cache
from itertools import combinations,product
import json,collections,time
HERE=Path(__file__).resolve().parent

def cross(a,b):
    return any((u<x<v<y) or (x<u<y<v) for u,v in combinations(a,2) for x,y in combinations(b,2))

def partitions(items):
    if not items:yield ();return
    for k in (2,3):
        for rest in combinations(items[1:],k-1):
            block=(items[0],)+rest;rem=tuple(x for x in items if x not in block)
            for tail in partitions(rem):yield (block,)+tail

@lru_cache(None)
def local(n):
    return tuple(bs for bs in partitions(tuple(range(n))) if not any(cross(a,b) for a,b in combinations(bs,2)))

@lru_cache(None)
def cuts(n,bs):
    out=[]
    # Partition the certificate BLOCKS into two sides, with the block of rank0 fixed.
    for mask in range((1<<(len(bs)-1))-1):
        side=set(bs[0])
        for j,b in enumerate(bs[1:]):
            if mask>>j&1:side.update(b)
        out.append(sum(1<<(i-1) for i in side if i))
    return tuple(out)

def original_facets(p):
    gs=[tuple(i for i,x in enumerate(p) if x==a) for a in sorted(set(p))]
    fs=set();count=0
    for choice in product(*(local(len(g)) for g in gs)):
        bs=[tuple(g[i] for i in b) for g,cs in zip(gs,choice) for b in cs]
        if any(cross(a,b) for a,b in combinations(bs,2)):continue
        count+=1
        fs.add(frozenset((a,t) for a,(g,cs) in enumerate(zip(gs,choice)) for t in cuts(len(g),cs)))
    return fs,count

def maxfaces(fs):
    return {f for f in fs if not any(f<g for g in fs)}

def allfaces(fs):
    F=set()
    for f in fs:
        for k in range(len(f)+1):F.update(map(frozenset,combinations(f,k)))
    return F

def unpack(fs):return {frozenset(map(tuple,f)) for f in fs}

def strong(fs,steps):
    fs=maxfaces(fs)
    for pair in steps:
        v,w=map(tuple,pair)
        assert v!=w and any(v in f for f in fs)
        assert all(w in f for f in fs if v in f)
        fs=maxfaces({f-{v} for f in fs})
    return fs

def elementary(F,steps):
    F=set(F)
    for pair in steps:
        s,t=map(lambda x:frozenset(map(tuple,x)),pair)
        assert s in F and t in F and s<t and len(t)==len(s)+1
        assert {u for u in F if s<=u}=={s,t}
        F.remove(s);F.remove(t)
    return F

start=time.time();checks=collections.Counter()
base=json.loads((HERE/'collapse_certificates.json').read_text())
for r in base:
    fs,m=original_facets(tuple(r['p']))
    assert fs==unpack(r['facets']) and m==r['generators']
    red=strong(fs,r['steps']);assert red==unpack(r['remaining'])
    assert len(set().union(*red))==1
    checks['base_collapses']+=1
rows={tuple(r['p']):r for r in json.loads((HERE/'holdout.json').read_text())['rows']}
traces=json.loads((HERE/'holdout_collapses.json').read_text())
element={tuple(r['p']):r for r in json.loads((HERE/'decision.json').read_text())['residuals']}
for tr in traces:
    p=tuple(tr['p']);fs,m=original_facets(p);assert m==rows[p]['generators']
    red=strong(fs,tr['steps']);assert red==unpack(tr['remaining'])
    F=allfaces(red);assert sum((-1)**len(f) for f in F)==rows[p]['coefficient']
    if p in element:
        e=element[p];rem=elementary(F,e['elementary_steps']);assert rem==unpack(e['remaining'])
        assert len(set().union(*rem))==1;checks['elementary_collapses']+=1
    checks['holdout_structural_checks']+=1
print('PASS',dict(checks),'seconds',time.time()-start,flush=True)
if (HERE/'deep_holdout.json').exists():
    rows={tuple(r['p']):r for r in json.loads((HERE/'deep_holdout.json').read_text())['rows'] if 'coefficient' in r}
    for tr in json.loads((HERE/'deep_traces.json').read_text()):
        p=tuple(tr['p']);fs,m=original_facets(p);assert m==rows[p]['generators']
        red=strong(fs,tr['strong_steps']);F=allfaces(red)
        assert sum((-1)**len(f) for f in F)==rows[p]['coefficient']
        rem=elementary(F,tr['elementary_steps']);assert rem==unpack(tr['remaining'])
        checks['deep_structural_checks']+=1
out=dict(status='VERIFIED-COMP',independent=True,checks=dict(checks),local_catalogue_sizes={n:len(local(n)) for n in range(5,11)},seconds=time.time()-start)
(HERE/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',json.dumps(out),flush=True)
