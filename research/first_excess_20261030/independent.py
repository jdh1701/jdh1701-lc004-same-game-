"""Global-certificate census, independent of the C++ local compatibility tables.

Generate complete NC 2/3 certificates on sixteen ORIGINAL positions; group their
blocks into two five-classes and one six-class. Compute separator faces directly
from these original blocks. Check small families again by direct subset joins.
"""
from pathlib import Path
from itertools import combinations,product
from collections import defaultdict,Counter
import sys,json,time,math
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from verify_global_nc_bridge import nc_certificates

def cross(a,b):
    # Scan original positions, unlike the C++ compressed pair-table lookup.
    word=[bool(a>>i&1) for i in range(16) if (a|b)>>i&1]
    return sum(i==0 or word[i]!=word[i-1] for i in range(len(word)))>=4

def connected(gs):
    # Exhaust all proper coarsenings of the three classes (five partitions total).
    if not any(cross(a,b) for a,b in combinations(gs,2)):return False
    return all(cross(gs[i],gs[(i+1)%3]|gs[(i+2)%3]) for i in range(3))

def cuts(classmask,bs):
    bs=sorted(bs,key=lambda b:b&-b);out=[]
    for mask in range((1<<(len(bs)-1))-1):
        side=bs[0]
        for i,b in enumerate(bs[1:]):
            if mask>>i&1:side|=b
        out.append((classmask<<16)|side)
    return out

def face_value(gs,cs):
    F=set()
    for bs in cs:
        facet=[]
        for g in gs:facet.extend(cuts(g,[b for b in bs if b&g==b]))
        for m in range(1<<len(facet)):F.add(frozenset(v for i,v in enumerate(facet) if m>>i&1))
    return sum((-1)**len(f) for f in F)

def direct_value(gs,cs):
    total=0
    for m in range(1,1<<len(cs)):
        parent=list(range(16))
        def root(i):
            while i!=parent[i]:i=parent[i]
            return i
        for j,bs in enumerate(cs):
            if m>>j&1:
                for B in bs:
                    vs=[i for i in range(16) if B>>i&1]
                    for v in vs[1:]:parent[root(v)]=root(vs[0])
        if all(len({root(i) for i in range(16) if g>>i&1})==1 for g in gs):total+=(-1)**(m.bit_count()+1)
    return total

def full_join(gs,cs):
    rel=[1<<i for i in range(16)]
    for bs in cs:
        for B in bs:
            merged=0
            for i in range(16):
                if B>>i&1:merged|=rel[i]
            for i in range(16):
                if merged>>i&1:rel[i]=merged
    return all(rel[(g&-g).bit_length()-1]==g for g in gs)

start=time.monotonic();certs=[];by=defaultdict(list);catalogue_hist={}
for pairs,triples in [(5,2),(2,4)]:
    count=0
    for bs0 in nc_certificates(pairs,triples):
        bs=tuple(sum(1<<i for i in b) for b in bs0);idx=len(certs);certs.append(bs);count+=1
        ps=[b for b in bs if b.bit_count()==2];ts=[b for b in bs if b.bit_count()==3]
        seen=set()
        for p,q in combinations(ps,2):
            for t,u in product(ts,repeat=2):
                if t==u:continue
                a,b=p|t,q|u
                if (a&-a)>(b&-b):a,b=b,a
                key=(a,b,65535^a^b)
                assert key not in seen;seen.add(key);by[key].append(idx)
    expected=math.factorial(16)//(math.factorial(17-pairs-triples)*math.factorial(pairs)*math.factorial(triples))
    assert count==expected;catalogue_hist[str((pairs,triples))]=count
print('global certificates',catalogue_hist,'pattern incidences',sum(map(len,by.values())),'patterns',len(by),flush=True)
survivors={};hist=Counter();genhist=Counter();full=0;checks=0;zero_checks=0;connected_count=0
for gs,ids in by.items():
    if not connected(gs):continue
    connected_count+=1;cs=[certs[i] for i in ids];v=face_value(gs,cs);hist[v]+=1
    if full_join(gs,cs):full+=1
    if v:
        assert direct_value(gs,cs)==v;checks+=1;survivors[gs]=(v,len(cs));genhist[len(cs)]+=1
    elif len(cs)<=8 and zero_checks<500:
        assert direct_value(gs,cs)==0;zero_checks+=1
    if connected_count%20000==0:print('evaluated',connected_count,flush=True)
expected={tuple(row[:3]):tuple(row[3:]) for row in (list(map(int,line.split())) for line in (HERE/'nonzero.txt').read_text().splitlines())}
assert survivors==expected
cpp=json.loads((HERE/'count.json').read_text())
assert connected_count==cpp['with_generators'] and full==cpp['full_join']
assert sum(v[0] for v in survivors.values())==cpp['coefficient_sum']==-312
assert len(survivors)==312 and genhist==Counter({2:88,3:224})
out=dict(status='VERIFIED-COMP',independent_global_certificate_census=True,global_catalogue=catalogue_hist,pattern_incidences=sum(map(len,by.values())),patterns_with_certificates=len(by),connected_patterns_with_certificates=connected_count,full_join=full,nonzero=len(survivors),coefficient_sum=sum(v[0] for v in survivors.values()),histogram_with_generators=dict(hist),nonzero_generator_histogram=dict(genhist),direct_nonzero_subset_checks=checks,direct_zero_subset_checks=zero_checks,seconds=time.monotonic()-start)
(HERE/'independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
