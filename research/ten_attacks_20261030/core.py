"""Exact original-position tools. No presumed kernel classification."""
from functools import lru_cache
from itertools import combinations, product
from collections import defaultdict
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research'))
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from certificate_join_count import join, canonical, wins
from verify_global_nc_bridge import nc_certificates

@lru_cache(None)
def catalogue(n):
    return tuple(canonical(bs,n) for t in range(n//3+1) if (n-3*t)%2==0
                 for bs in nc_certificates((n-3*t)//2,t))

def blocks(p):
    return tuple(tuple(i for i,c in enumerate(p) if c==a) for a in sorted(set(p)))

def crossing(a,b):
    return any(u<x<v<y or x<u<y<v for u,v in combinations(a,2) for x,y in combinations(b,2))

def maximal(fs):
    fs=set(map(frozenset,fs))
    return tuple(sorted((f for f in fs if not any(f<g for g in fs)),key=lambda s:(len(s),sorted(s))))

def faces(fs):
    out=set()
    for f in fs:
        f=tuple(f)
        out.update(frozenset(f[i] for i in range(len(f)) if mask>>i&1) for mask in range(1<<len(f)))
    return out

@lru_cache(None)
def local_facets(n):
    out=[]
    for c in catalogue(n):
        out.append(frozenset(t for t in range((1<<(n-1))-1)
            if all(c[i]!=c[j] or (1 if i==0 else (t>>(i-1))&1)==(1 if j==0 else (t>>(j-1))&1)
                   for i in range(n) for j in range(i))))
    return tuple(out)

def generators(p):
    gs=blocks(p);cats=[catalogue(len(g)) for g in gs];out=[];facets=[];choices=[]
    for inds in product(*(range(len(cs)) for cs in cats)):
        bs=[];f=set()
        for a,(g,cs,s) in enumerate(zip(gs,cats,inds)):
            bs.extend(tuple(g[i] for i in b) for b in blocks(cs[s]))
            f.update((a,t) for t in local_facets(len(g))[s])
        if not any(crossing(a,b) for a,b in combinations(bs,2)):
            out.append(canonical(bs,len(p)));facets.append(frozenset(f));choices.append(inds)
    return tuple(out),tuple(facets),tuple(choices)

def join_value(cs,p):
    acc={}
    for c in cs:
        delta=defaultdict(int);delta[c]+=1
        for old,v in acc.items():delta[join(old,c)]-=v
        for q,v in delta.items():
            acc[q]=acc.get(q,0)+v
            if not acc[q]:del acc[q]
    return acc.get(p,0)

def full_join(cs,n):
    q=tuple(range(n))
    for c in cs:q=join(q,c)
    return q

def strong_collapse(fs):
    fs=maximal(fs);steps=[]
    while fs:
        vs=set().union(*fs)
        pair=None
        for v in sorted(vs):
            containing=[f for f in fs if v in f]
            dom=set.intersection(*(set(f) for f in containing))-{v}
            if dom:pair=(v,min(dom));break
        if pair is None:break
        v,w=pair;steps.append(pair);fs=maximal(f-{v} for f in fs)
    return fs,steps

def rank_f2(cols):
    piv={}
    for x in cols:
        while x:
            p=x.bit_length()-1
            if p in piv:x^=piv[p]
            else:piv[p]=x;break
    return len(piv)

def homology_f2(F):
    by={k:sorted((f for f in F if len(f)==k),key=lambda s:sorted(s)) for k in range(max(map(len,F),default=0)+1)}
    ranks={}
    for k in range(1,len(by)):
        rows={s:i for i,s in enumerate(by[k-1])}
        ranks[k]=rank_f2([sum(1<<rows[f-{v}] for v in f) for f in by[k]])
    return [len(by[k])-ranks.get(k,0)-ranks.get(k+1,0) for k in range(len(by))]

def two_patterns(a,b):
    n=a+b
    for g in combinations(range(n),a):
        if a==b and 0 not in g:continue
        gs=set(g);p=tuple(int(i not in gs) for i in range(n))
        if p[0]:p=tuple(1-x for x in p)
        yield p
