"""Exact finite inputs and regression tests for the uniform paper argument.
No census bound is used to infer the unbounded conclusion. All state numbers
here match LocalCertificateCatalogues.lean, NOT core.py catalogue numbers.
"""
from pathlib import Path
from itertools import combinations, product
from collections import Counter
from functools import reduce
import json, sys, hashlib
ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'research/ten_attacks_20261030'))
import core
C5 = tuple(tuple(map(int, s)) for s in ['00011','00110','00111','01100','01110'])
C6 = tuple(tuple(map(int, s)) for s in ['000111','001110','001122','001221','011022','011100','011220','012210'])
FULL = 255
MASKS = (0,1,2,4,8,16,32,64,128,12,20,132,72,80,192,255)
EDGES = tuple(tuple(i for i in range(8) if m >> i & 1) for m in MASKS[9:15])
TRIPLES = {0,1,5}

def cross(a,b):
    # Different implementation from core.crossing: a chord separates b iff
    # b has a point strictly inside and a point strictly outside it.
    return any(any(u < x < v for x in b) and any(x < u or v < x for x in b)
               for u,v in combinations(a,2))

def valid(bs):
    return not any(cross(a,b) for a,b in combinations(bs,2))

def on(g,c):
    return tuple(tuple(g[i] for i in b) for b in core.blocks(c))

def rows_for(g,h):
    return tuple(sum(1 << t for t,d in enumerate(C6) if valid(on(g,c)+on(h,d))) for c in C5)

def classify(R):
    A=[i for i,r in enumerate(R) if r]
    B=reduce(int.__or__,R,0)
    if not A:return 'empty'
    if all(R[i]==B for i in A):return 'universal'
    if all(R[i].bit_count()==1 for i in A) and len({R[i] for i in A})==len(A):
        assert len(A)==2
        return 'bijection2'
    for a in A:
        for b in range(5):
            if B>>b&1 and all(R[x]==(B if x==a else 1<<b) for x in A):return 'twofan'
    raise AssertionError(R)

def faces(A):
    out=set()
    for a in A:
        f=tuple(enumerate(a))
        out.update(frozenset(f[i] for i in range(len(f)) if m>>i&1) for m in range(1<<len(f)))
    return out

def beta(F):return sum((-1)**len(f) for f in F)

def fibre(a,rows):return reduce(int.__and__,(R[s] for R,s in zip(rows,a)),FULL)

for n,C in [(5,C5),(6,C6)]:
    assert set(C)==set(core.catalogue(n))
    assert len(set(C))==len(C)
# Exact original positions, all 462 order types; no support pruning here.
rows=[]
for g in combinations(range(11),5):
    h=tuple(x for x in range(11) if x not in g)
    R=rows_for(g,h)
    assert all(r in MASKS for r in R)
    assert cross(g,h)==core.crossing(g,h)
    if cross(g,h):assert sum(r==FULL for r in R)<=1
    else:assert R==(FULL,)*5
    nonempty=[i for i in range(5) if R[i]]
    for k in range(3,6):
        for S in combinations(nonempty,k):assert reduce(int.__and__,(R[i] for i in S),FULL)
    rows.append({'five':g,'rows':R})
rels=sorted({tuple(r['rows']) for r in rows})
assert len(rels)==154
assert {x for R in rels for x in R}==set(MASKS)
for a,b in product(MASKS,repeat=2):assert a&b in MASKS
for a,b,c in product(MASKS,repeat=3):
    if a&b and a&c and b&c:assert a&b&c
stats=Counter()
for A,B in product(rels,repeat=2):
    R=tuple(sum(1<<j for j in range(5) if A[i]&B[j]) for i in range(5))
    stats[classify(R)]+=1
# Catalogue incidence, including empty intersections.
facets=[]
for c in C6:
    facets.append({mask for mask in range(31) if all(c[i]!=c[j] or
        (1 if i==0 else (mask>>(i-1))&1)==(1 if j==0 else (mask>>(j-1))&1)
        for i in range(6) for j in range(i))})
assert {tuple((s,t)) for s,t in combinations(range(8),2) if facets[s]&facets[t]}==set(EDGES)
assert all(not(facets[s]&facets[t]&facets[u]) for s,t,u in combinations(range(8),3))
fibre_types=Counter()
for a,b in product(MASKS,repeat=2):
    if not a or not b or a&b:continue
    if any((a>>s&1 and b>>t&1) or (a>>t&1 and b>>s&1) for s,t in EDGES):continue
    sizes=sorted([a.bit_count(),b.bit_count()])
    assert sizes in ([1,1],[1,2])
    if sizes==[1,2]:assert next(i for i in range(8) if (a if a.bit_count()==1 else b)>>i&1) in TRIPLES
    fibre_types[str(sizes)]+=1
# The finite cases in the last run argument, before the four-gap switch.
preserving=splitting=0
for s,t in EDGES:
    P=next(iter(set(core.blocks(C6[s])) & set(core.blocks(C6[t]))))
    for z in TRIPLES:
        common={i for i in range(6) if C6[z][i]==C6[z][(i+1)%6] and
                (C6[s][i]==C6[s][(i+1)%6] or C6[t][i]==C6[t][(i+1)%6])}
        if C6[z][P[0]]==C6[z][P[1]]:
            preserving+=1
            assert any((i+1)%6 in common for i in common)
        else:
            splitting+=1
            assert len(common)==2
            assert len({x for i in common for x in (i,(i+1)%6)})==4
            assert {x for i in common for x in (i,(i+1)%6)}==set(range(6))-set(P)
            # Dihedral normalization to P=01, T=011100, M=001122/001221.
            assert any(
                {tuple(sorted((eps*i+k)%6 for i in P))}=={(0,1)} and
                {tuple(sorted((eps*i+k)%6 for i in b)) for b in core.blocks(C6[z])}==set(core.blocks(C6[5]))
                for eps in (1,-1) for k in range(6))
Tcell=(0,1,0,2);Qcell=(0,1,2,1)
region_cases=0
for r,u,v in product(range(4),repeat=3):
    if Tcell[r]==Tcell[u] and Qcell[r]==Qcell[v]:
        region_cases+=1
        assert r%2==u%2==v%2
        assert r%2 or r==v
        assert not r%2 or r==u
# Retain the failed pair-adjacency-only shortcut in the CURRENT catalogue order.
g=(0,1,2,5,6);h=tuple(x for x in range(11) if x not in g)
R=rows_for(g,h)
a=C5.index(core.catalogue(5)[2]);b=C5.index(core.catalogue(5)[0])
s=C6.index(core.catalogue(6)[0]);t=C6.index(core.catalogue(6)[1]);z=C6.index(core.catalogue(6)[7])
assert R[a]>>z&1 and R[b]>>s&1 and R[b]>>t&1 and not R[b]>>z&1
failed={'five':g,'six':h,'a':a,'b':b,'s':s,'t':t,'z':z,'rows':R}
# Regression on the existing COMPLETE n21 full-join representative census.
# This checks the Euler identity and its cancellation witnesses on zero as well
# as nonzero coefficients; it does not substitute for the uniform proof.
reg=Counter()
for lineno,line in enumerate((ROOT/'research/first_excess_20261031/full_join.txt').read_text().splitlines()):
    vals=list(map(int,line.split()))
    gs=[tuple(x for x in range(21) if m>>x&1) for m in vals[:4]]
    h=next(g for g in gs if len(g)==6); gs=[g for g in gs if len(g)==5]
    Rs=[rows_for(g,h) for g in gs]
    opts=[[on(g,c) for c in C5] for g in gs]
    A0=[a for a in product(range(5),repeat=3) if valid(sum((opts[i][s] for i,s in enumerate(a)),()))]
    A={a for a in A0 if fibre(a,Rs)}
    P=faces(A);B=beta(faces(A0));kp=beta(P)
    Ks=[faces([a for a in A0 if fibre(a,Rs)>>t&1]) for t in range(8)]
    kt=list(map(beta,Ks));es=[-beta(Ks[s]&Ks[t]) for s,t in EDGES]
    calc=kp-sum(kt)-sum(es)
    assert calc==vals[-2],(lineno,calc,vals)
    us=[all(not cross(bl,g) for bl in on(h,c) for g in gs) for c in C6]
    vs=[]
    for s,t in EDGES:
        q=core.join(C6[s],C6[t])
        vs.append(all(not cross(bl,g) for bl in on(h,q) for g in gs))
    assert kt==[B if u else 0 for u in us]
    assert es==[-B if v else 0 for v in vs]
    assert sum(us)-sum(vs) in (0,1)
    assert calc==kp-(sum(us)-sum(vs))*B
    reg['full_join_representatives']+=1
    if calc:
        assert not any(us) and not any(vs)
        assert calc==kp==-1 and len(A)==2
        aa,bb=sorted(A)
        assert all(x!=y for x,y in zip(aa,bb))
        fs=(fibre(aa,Rs),fibre(bb,Rs))
        ngen=sum(m.bit_count() for m in fs)
        assert ngen==vals[-1] and ngen in (2,3)
        three=any(all((h[(i+k)%6]-h[i])%21==k for k in range(3)) for i in range(6))
        assert three==(ngen==3)
        reg['nonzero_representatives']+=1
        reg[f'certificates_{ngen}']+=1
    if lineno%1000==0:print('regression',lineno,flush=True)
result={'interleavings':len(rows),'distinct_matrices':len(rels),'boundary_masks':MASKS,
        'composed_relations':dict(sorted(stats.items())),'six_edges':EDGES,
        'fibre_types':dict(sorted(fibre_types.items())),
        'pair_preserving_triples':preserving,'pair_splitting_triples':splitting,
        'four_gap_cases':region_cases,'failed_shortcut':failed,'regression':dict(sorted(reg.items()))}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'boundary_tables.json').write_text(json.dumps({'catalogue5':C5,'catalogue6':C6,'interleavings':rows},indent=2)+'\n')
print(json.dumps(result,indent=2))
