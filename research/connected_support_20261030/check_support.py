"""Exact adversarial checks for the connected 5j support theorem.

NC closure by crossing merges is checked against saturated interval cuts.
Nonzero connected multi-class coefficients also get a raw-game Mobius check.
"""
from pathlib import Path
import sys,json,time,itertools as it,math,collections
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research'))
from certificate_join_count import join,patterns
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from verify_global_nc_bridge import nc_certificates

def groups(p):
    return [tuple(i for i,x in enumerate(p) if x==a) for a in sorted(set(p))]
def crossed(A,B):
    return any(a<b<c<d or b<a<d<c for a,c in it.combinations(A,2) for b,d in it.combinations(B,2))
def connected(p):
    gs=list(map(set,groups(p)))
    while True:
        edge=next(((i,j) for i in range(len(gs)) for j in range(i) if crossed(sorted(gs[i]),sorted(gs[j]))),None)
        if edge is None:return len(gs)<=1
        i,j=edge;gs[j]|=gs[i];gs.pop(i)
def interval_connected(p):
    n=len(p)
    return not any(all(all(l<=i<r for i in g) or all(not l<=i<r for i in g) for g in groups(p))
        for l in range(n) for r in range(l+1,n+1) if r-l<n)
def canon(bs,n):
    w=[0]*n
    for a,b in enumerate(bs):
        for i in b:w[i]=a
    return tuple(w)
def coefficients(n):
    weights={};count=0
    for t in range(n//3+1):
        if (n-3*t)%2:continue
        for bs in nc_certificates((n-3*t)//2,t):
            c=canon(bs,n);count+=1;delta=collections.defaultdict(int);delta[c]+=1
            for p,v in weights.items():delta[join(p,c)]-=v
            for p,v in delta.items():
                weights[p]=weights.get(p,0)+v
                if not weights[p]:del weights[p]
    return weights,count
@lru_cache(None)
def raw_win(w):
    if not w:return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2 and raw_win(w[:i]+w[j:]):return True
        i=j
    return False
@lru_cache(None)
def refinements(points):
    if not points:return ((),)
    out=[];a=points[0]
    for k in range(2,len(points)+1):
        for tail in it.combinations(points[1:],k-1):
            block=(a,)+tail;rest=tuple(x for x in points if x not in block)
            out.extend((block,)+bs for bs in refinements(rest))
    return tuple(out)
def raw_mobius(p):
    total=0;count=0
    for chunks in it.product(*(refinements(g) for g in groups(p))):
        mu=math.prod((-1)**(len(c)-1)*math.factorial(len(c)-1) for c in chunks)
        word=canon(tuple(b for c in chunks for b in c),len(p))
        total+=mu*raw_win(word);count+=1
    return total,count

geometry=0
for n in range(9):
    for p,k in patterns(n):
        assert connected(p)==interval_connected(p)
        if connected(p) and k>=2:
            gs=groups(p)
            assert all(any(A!=B and crossed(A,B) for B in gs) for A in gs)
        geometry+=1
print('GEOMETRY',geometry,'patterns through n=8',flush=True)
rows=[];witnesses=[];start=time.monotonic();raw_checks=0
for n in range(12):
    weights,gencount=coefficients(n);polynomial=collections.Counter();multi=0
    for p,value in weights.items():
        if not connected(p):continue
        k=len(set(p));polynomial[k]+=value
        assert k<=max(1,n//5),(p,value)
        if k>=2:
            assert min(map(len,groups(p)))>=5 and 5*k<=n
            check,count=raw_mobius(p);assert check==value
            raw_checks+=1;multi+=1
            witnesses.append(dict(p=p,coefficient=value,raw_refinements=count))
    rows.append(dict(n=n,generators=gencount,nonzero_patterns=len(weights),connected_polynomial=dict(sorted(polynomial.items())),connected_multiclass_nonzero=multi))
    print('PASS',rows[-1],flush=True)
    (HERE/'support-check.partial.json').write_text(json.dumps(dict(geometry=geometry,rows=rows,witnesses=witnesses)))
# Both necessary hypotheses have concrete negative controls.
w4,_=coefficients(4);assert w4[(0,0,1,1)]==1 and not connected((0,0,1,1))
w2,_=coefficients(2);assert w2[(0,0)]==1 and connected((0,0))
out=dict(status='VERIFIED-COMP',geometry_patterns=geometry,max_coefficient_n=11,raw_checks=raw_checks,rows=rows,witnesses=witnesses,
    controls=dict(disconnected='0011: coefficient1, n=4<10',one_class='00: coefficient1, n=2<5'),seconds=time.monotonic()-start)
(HERE/'support-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE raw checks',raw_checks,'seconds',out['seconds'],flush=True)
