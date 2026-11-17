"""Finite inflation equality, whole-class deletion failures, and direct
proper-coarsening connectivity controls. No inferred all-length recurrence."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import json,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler
from core import blocks,crossing,two_patterns
def norm(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
def orbit(p):return {norm(q[t:]+q[:t]) for q in (p,p[::-1]) for t in range(len(p))}
def rgs(n):
    if n==0:yield ();return
    for p in rgs(n-1):
        for x in range(max(p,default=-1)+2):yield p+(x,)
def connected(p):
    gs=blocks(p)
    for q in rgs(len(gs)):
        if len(set(q))==1:continue
        merged=[tuple(sorted(x for k,g in enumerate(gs) if q[k]==a for x in g)) for a in set(q)]
        if not any(crossing(a,b) for a,b in combinations(merged,2)):return False
    return True
def runs(p):
    starts=[i for i in range(len(p)) if p[i]!=p[(i-1)%len(p)]]
    return [(i,(starts[(k+1)%len(starts)]-i)%len(p)) for k,i in enumerate(starts)]
rows=json.loads((HERE/'replay.json').read_text())['rows']
parents=set();three=set();two=set()
for r in rows:
    p=tuple(r['p']);assert connected(p)
    if r['generators']==2:two.update(orbit(p));continue
    three.update(orbit(p))
    i=next(i for i,size in runs(p) if size==3)
    q=norm(p[:i]+p[i+1:]);d=encode(q)
    assert connected(q) and d['generators']==2 and euler(d['facets'])==-1
    parents.update(orbit(q))
assert len(parents)==415 # matches the earlier independent complete all-five census
children=set()
for p in parents:
    for a in set(p):assert sorted(size for i,size in runs(p) if p[i]==a)==[1,2,2]
    for i,size in runs(p):
        if size==2:children.update(orbit(norm(p[:i]+(p[i],)+p[i:])))
assert children==three and len(three)==3486 and len(two)==2121 and not (three&two)
assert 5*len(children)==2*21*len(parents)
deletions16=Counter();failures16=[]
for r in json.loads((ROOT/'research/first_excess_20261030/classification.json').read_text())['dihedral_representatives']:
    p=r['p'];good=[]
    for a in set(p):
        if p.count(a)!=5:continue
        q=norm(x for x in p if x!=a);d=encode(q)
        if connected(q) and euler(d['facets'])!=0:good.append(a)
    deletions16[str((len(r['generators']),len(good)))]+=r['orbit_size']
    if not good:failures16.append(dict(p=p,orbit_size=r['orbit_size'],generators=len(r['generators'])))
j2=Counter()
for p in two_patterns(5,6):
    if connected(p):
        d=encode(p);j2[euler(d['facets'])]+=1
out=dict(status='VERIFIED-COMP',n21_three_generator_patterns=len(three),n21_inflation_image=len(children),n20_parents=len(parents),n21_two_generator_patterns=len(two),n21_no_five_class_deletion=sum(r['six_subset_orbit_weight'] for r in rows if not r['successful_class_deletions']),n16_class_deletion_histogram=dict(deletions16),n16_no_five_class_deletion=sum(r['orbit_size'] for r in failures16),n16_deletion_counterexamples=failures16,n11_connected_coefficient_histogram=dict(j2),scope='Finite identities only; all-length run structure, inflation preservation and enumeration remain unproved.')
(HERE/'structure.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
