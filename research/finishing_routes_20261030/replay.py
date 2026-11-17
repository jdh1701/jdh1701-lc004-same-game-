"""Independent replay of the decisive counterexamples.

Uses unrestricted 2/3-block partitions filtered by crossings; direct signed
subset joins (not separator Euler values); determinant evaluation (not traces).
Imports no search helper.
"""
from pathlib import Path
from itertools import combinations,product
from fractions import Fraction
from functools import lru_cache
import json,math
HERE=Path(__file__).resolve().parent
def read(name):return json.loads((HERE/(name+'.json')).read_text())
def cross(a,b):return any(u<x<v<y or x<u<y<v for u,v in combinations(a,2) for x,y in combinations(b,2))
def nc(bs):return not any(cross(a,b) for a,b in combinations(bs,2))
def parts(xs):
    if not xs:yield ();return
    for k in (2,3):
        for tail in combinations(xs[1:],k-1):
            B=(xs[0],)+tail
            for rest in parts(tuple(x for x in xs if x not in B)):yield (B,)+rest
@lru_cache(None)
def local(n):return tuple(bs for bs in parts(tuple(range(n))) if nc(bs))
def groups(p):return [tuple(i for i,x in enumerate(p) if x==a) for a in sorted(set(p))]
def canon(bs,n):
    out=[None]*n
    for a,B in enumerate(sorted(bs)):
        for i in B:out[i]=a
    assert None not in out
    return tuple(out)
def certificates(p):
    gs=groups(p);out=[]
    for choice in product(*(local(len(g)) for g in gs)):
        bs=tuple(tuple(g[i] for i in b) for g,cs in zip(gs,choice) for b in cs)
        if nc(bs):out.append((canon(bs,len(p)),choice))
    return out
def join_all(cs,n):
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:i=parent[i]
        return i
    for c in cs:
        for B in groups(c):
            for v in B[1:]:parent[root(v)]=root(B[0])
    return canon(tuple(tuple(i for i in range(n) if root(i)==r) for r in sorted({root(i) for i in range(n)})),n)
def coefficient(p):
    cs=[x[0] for x in certificates(p)];total=0
    assert len(cs)<=16
    for k in range(1,len(cs)+1):
        total+=(-1)**(k+1)*sum(join_all(sub,len(p))==tuple(p) for sub in combinations(cs,k))
    return total
def facets(p):
    out=[]
    for _,choice in certificates(p):
        f=set()
        for a,bs in enumerate(choice):
            for mask in range((1<<(len(bs)-1))-1):
                side=set(bs[0])
                for j,B in enumerate(bs[1:]):
                    if mask>>j&1:side.update(B)
                f.add((a,sum(1<<(i-1) for i in side if i)))
        out.append(frozenset(f))
    return set(f for f in out if not any(f<g for g in out))
def det(M):
    A=[list(map(Fraction,row)) for row in M];out=Fraction(1);n=len(A)
    for i in range(n):
        pivot=next((j for j in range(i,n) if A[j][i]),None)
        if pivot is None:return 0
        if pivot!=i:A[i],A[pivot]=A[pivot],A[i];out=-out
        v=A[i][i];out*=v
        for j in range(i+1,n):
            q=A[j][i]/v
            for k in range(i,n):A[j][k]-=q*A[i][k]
    assert out.denominator==1
    return int(out)
checks={}
w=read('03_matroid')['witness'];p=tuple(w['p']);cs=[tuple(c) for c in w['generators']]
assert set(cs)=={c for c,_ in certificates(p)}
bases=[]
for s in range(1,1<<len(cs)):
    if join_all([c for i,c in enumerate(cs) if s>>i&1],len(p))!=p:continue
    if all(join_all([c for i,c in enumerate(cs) if s>>i&1 and i!=j],len(p))!=p for j in range(len(cs)) if s>>j&1):bases.append(s)
assert bases==w['bases'] and sorted({s.bit_count() for s in bases})==[2,3]
checks['matroid_complete_minimal_basis_family']=len(bases)
w=read('04_flag')['witness'];fs=facets(w['p']);labels=list(map(tuple,w['labels']))
assert fs=={frozenset(labels[i] for i in range(len(labels)) if f>>i&1) for f in w['facets']}
t=frozenset(labels[i] for i in w['missing_triangle'])
assert not any(t<=f for f in fs) and all(any(t-{v}<=f for f in fs) for v in t)
checks['flag_missing_triangle']=True
w=read('05_barrier_grammar')['witness'];p=w['p'];a=w['removed_class'];b=1-a
projected={frozenset((0,t) for cl,t in f if cl==b) for f in facets(p)}
projected={f for f in projected if not any(f<g for g in projected)}
unrestricted=facets((0,)*len(groups(p)[b]));assert projected!=unrestricted
checks['class_deletion_failure']=True
w=read('06_gram_spectrum_stress')['witness'];pol=w['gram_charpoly']
for side in ('first','second'):
    r=w[side];p=r['p'];assert coefficient(p)==r['coefficient']
    A=r['matrix'];B=[[sum(x*y for x,y in zip(u,v)) for v in A] for u in A];n=len(B)
    assert len(pol)==n+1
    for t in range(n+1):
        assert det([[int(i==j)*t-B[i][j] for j in range(n)] for i in range(n)])==sum(c*t**(n-k) for k,c in enumerate(pol))
assert w['first']['coefficient']!=w['second']['coefficient']
checks['spectral_collision_determinant_evaluations']=2*len(pol)
w=read('07_hereditary_support')['witness'];assert coefficient(w['p'])==-1 and coefficient(w['restriction'])==0
assert cross(*groups(w['restriction']))
checks['heredity_failure_original_signed_joins']=True
w=read('09_shallow_side')['witness'];certs={c for c,_ in certificates(w['p'])}
assert len(certs)==2 and certs=={canon(bs,len(w['p'])) for bs in w['certificates']}
assert all(any(max(B)-min(B)+1!=len(B) for B in groups(c)) for c in certs)
checks['interval_hypothesis_failure']=True
w=read('08_scc_species')['witness'];gs=groups(w['p']);opts=[]
for G in gs:opts.append([(P,tuple(x for x in G if x not in P)) for P in combinations(G,2) if nc((P,tuple(x for x in G if x not in P)))])
a,b=w['pair']
assert nc(tuple(B for i in range(2) for B in opts[i][a[i]])) and nc(tuple(B for i in range(2) for B in opts[i][b[i]]))
edges=[[i,j] for i,j in product(range(2),repeat=2) if i!=j and not nc(opts[i][b[i]]+opts[j][a[j]])]
assert edges==w['edges']==[[1,0]] and cross(*w['coarsened_blocks'])
checks['scc_non_noncrossing_failure']=True
support=json.loads((HERE.parent/'connected_support_20261030/support-check.json').read_text())
inter=read('02_interpolation')['coefficients']
for row in support['rows'][1:]:
    values=inter[row['n']-1]['coefficients'];actual={int(k):v for k,v in row['connected_polynomial'].items() if v}
    assert {j:v for j,v in enumerate(values) if v}==actual
checks['interpolation_independent_support_polynomials']=11
out=dict(status='VERIFIED-COMP',independent=True,checks=checks)
(HERE/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
