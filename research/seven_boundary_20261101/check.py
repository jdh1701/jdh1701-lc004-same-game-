"""Seven-class boundary: exact 3-Helly elimination and an Euler reduction.
Counterexamples deliberately distinguish raw matrices from a realized source.
Catalogue order is core.py's; the complete catalogues are saved in checks.json.
"""
from pathlib import Path
from itertools import combinations,product
from collections import Counter
from functools import reduce
import json,sys
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import catalogue,blocks,crossing,generators,join_value,local_facets,canonical
C5=catalogue(5);C7=catalogue(7);FULL=(1<<len(C7))-1

def placed(g,c):return tuple(tuple(g[i] for i in b) for b in blocks(c))
def good(bs):return not any(crossing(a,b) for a,b in combinations(bs,2))
def faces(A):
 out=set()
 for a in A:
  f=tuple(enumerate(a))
  out.update(frozenset(f[i] for i in range(len(f)) if m>>i&1) for m in range(1<<len(f)))
 return out
def beta(F):return sum((-1)**len(f) for f in F)
def shape(R):
 A=[i for i in range(5) if R[i]];B=reduce(int.__or__,R,0)
 if not A:return 'empty'
 if all(R[a]==B for a in A):return 'universal'
 if all(R[a].bit_count()==1 for a in A) and len({R[a] for a in A})==len(A):return 'bijection'
 for a in A:
  for b in range(5):
   if B>>b&1 and all(R[x]==(B if x==a else 1<<b) for x in A):return 'twofan'
 return 'not_majority_closed'
rels={};rowwitness={};allrows=[]
for G in combinations(range(12),5):
 H=tuple(x for x in range(12) if x not in G)
 A=[placed(G,c) for c in C5];B=[placed(H,c) for c in C7]
 R=tuple(sum(1<<t for t,bb in enumerate(B) if good(aa+bb)) for aa in A)
 rels.setdefault(R,G);allrows.append((G,H,R))
 for x,m in enumerate(R):rowwitness.setdefault(m,(G,x))
ms=sorted(rowwitness)
assert len(rels)==338 and len(ms)==37
assert all(a&b in rowwitness for a,b in product(ms,repeat=2))
helly_failure=next((a,b,c) for a,b,c in combinations(ms,3) if a&b and a&c and b&c and not a&b&c)
# Every minimal empty family containing a <=2-element list has size <=3.
# Thus a possible higher obstruction would use only the seven five-element
# lists (and the harmless universal list). Check all their subsets.
fives=[m for m in ms if m.bit_count()==5];assert len(fives)==7
assert all(m.bit_count()<=2 or m.bit_count()==5 or m==FULL for m in ms)
for mask in range(1<<7):
 F=[fives[i] for i in range(7) if mask>>i&1]
 if all(reduce(int.__and__,T,FULL) for k in range(1,4) for T in combinations(F,k)):
  assert reduce(int.__and__,F,FULL)
stats=Counter();first_bad=None
for A,B in product(rels,repeat=2):
 R=tuple(sum(1<<j for j in range(5) if A[i]&B[j]) for i in range(5))
 ty=shape(R);stats[ty]+=1
 if ty=='not_majority_closed' and first_bad is None:
  pairs=[(i,j) for i in range(5) for j in range(5) if R[i]>>j&1]
  for a,b,c in product(pairs,repeat=3):
   d=tuple(a[i] if a[i]==b[i] else c[i] for i in range(2))
   if not R[d[0]]>>d[1]&1:
    first_bad={'five1':rels[A],'five2':rels[B],'rows1':A,'rows2':B,'composed':R,'witness':[a,b,c,d]};break
  assert first_bad
# A REAL original (5,5,7) family, not merely independently chosen matrices.
p=(1,1,0,0,0,2,2,0,0,2,1,1,2,2,1,2,2)
cs,fs,ch=generators(p);A=sorted({a[:2] for a in ch})
w=[(4,0),(4,3),(2,4),(4,4)]
assert all(a in A for a in w[:3]) and w[3] not in A
assert tuple(w[0][i] if w[0][i]==w[1][i] else w[2][i] for i in range(2))==w[3]
assert join_value(cs,canonical(blocks(p),len(p)))==0
real={'pattern':p,'choices':ch,'outside_projection':A,'witness':w,'coefficient':0}
# Stronger original obstruction: nonzero coefficient, connected, complete
# seven-generator family. State coordinate order is numeric color order 0,1,2.
np=(0,2,2,0,1,1,2,2,1,2,2,1,1,0,0,2,0)
ncs,nfs,nch=generators(np);nA={a[:2] for a in nch}
nw=[(3,0),(3,2),(1,1),(3,1)]
assert len(nch)==7 and all(a in nA for a in nw[:3]) and nw[3] not in nA
assert tuple(nw[0][i] if nw[0][i]==nw[1][i] else nw[2][i] for i in range(2))==nw[3]
ng=blocks(np)
assert sum(crossing(a,b) for a,b in combinations(ng,2))>=2
assert join_value(ncs,canonical(ng,len(np)))==1
nonzero_failure={'pattern':np,'choices':nch,'outside_projection':sorted(nA),
                 'witness':nw,'coefficient':1,'class_crossing_connected':True}
# Pairwise boundary extension can fail even for one mutually noncrossing
# outside assignment. This is a raw binary-specification obstruction, not a
# claim about a nonempty family's exact pair projections.
hp=(0,0,1,1,1,1,0,0,2,2,2,3,3,0,3,2,3,3,2,1,3,3)
hg=[tuple(i for i,x in enumerate(hp) if x==c) for c in range(4)]
hs=(0,0,2)
hbs=sum((placed(g,C5[s]) for g,s in zip(hg,hs)),())
assert good(hbs)
hrows=[{t for t,c in enumerate(C7) if good(placed(g,C5[s])+placed(hg[3],c))}
       for g,s in zip(hg,hs)]
assert all(a&b for a,b in combinations(hrows,2)) and not set.intersection(*hrows)
assert not generators(hp)[0]
real_helly={'pattern':hp,'outside_state':hs,'boundary_lists':[sorted(x) for x in hrows],
            'complete_family_size':0}
# Local cut incidence. Every pair of distinct 3-block certificates shares at
# most one cut. The nonsingleton cut cliques are seven size5 and seven size2.
facets=local_facets(7);cuts=sorted(set().union(*facets))
inc={u:tuple(t for t,f in enumerate(facets) if u in f) for u in cuts}
assert Counter(map(len,inc.values()))==Counter({1:14,5:7,2:7})
assert all(len(facets[s]&facets[t])<=1 for s,t in combinations(range(21),2))
cliques=[(u,ts) for u,ts in inc.items() if len(ts)>1]
for u,ts in cliques:
 cut=tuple(1 if i==0 else (u>>(i-1))&1 for i in range(7))
 sizes=sorted(map(len,blocks(cut)))
 assert sizes==([2,5] if len(ts)==5 else [3,4])
 assert good(blocks(cut))
# The nonzero obstruction is a genuine cycle in the projected choice graph;
# every correction term vanishes separately in this particular example.
np_beta=beta(faces([a[:2] for a in nch]))
nk=[beta(faces([a[:2] for a in nch if a[2]==t])) for t in range(21)]
ne=[beta(faces([a for a in nch if a[2] in ts])) for u,ts in cliques]
assert np_beta==1 and not any(nk) and not any(ne)
nonzero_failure['projected_beta']=np_beta
nonzero_failure['state_corrections']=nk
nonzero_failure['cut_corrections']=ne
# Check the new Euler identity on every 5/7 order type, using original indexed
# facets. Also compare the original signed-join implementation on all crossed
# order types with at most 12 generators (the bound is a replay budget only).
replayed=0;crossed_replays=0
for G,H,R in allrows:
 ch=[(s,t) for s in range(5) for t in range(21) if R[s]>>t&1]
 A={a[:1] for a in ch};P=faces(A)
 K=[faces([a[:1] for a in ch if a[1]==t]) for t in range(21)]
 E=[faces([a for a in ch if a[1] in ts]) for u,ts in cliques]
 rhs=beta(P)-sum(map(beta,K))-sum(map(beta,E))
 # Direct original indexed facets: five-state choice vertex plus all seven cuts.
 F=set()
 for s,t in ch:
  facet=[('five',s)]+[('seven',u) for u in facets[t]]
  F.update(frozenset(facet[i] for i in range(len(facet)) if m>>i&1) for m in range(1<<len(facet)))
 assert rhs==beta(F)
 if crossing(G,H) and len(ch)<=12:
  p=canonical([G,H],12)
  # G need not be the zero-labelled class in canonical p; construct directly.
  certs=[canonical(placed(G,C5[s])+placed(H,C7[t]),12) for s,t in ch]
  assert rhs==join_value(certs,p)
  crossed_replays+=1
 replayed+=1
result={'catalogue5':C5,'catalogue7':C7,'order_types':len(allrows),'matrices':len(rels),
 'list_sizes':dict(sorted(Counter(x.bit_count() for x in ms).items())),
 'helly_number':3,'helly2_counterexample':[{'mask':m,'witness':rowwitness[m]} for m in helly_failure],
 'composed_relations':dict(sorted(stats.items())),'first_raw_failure':first_bad,'realized_failure':real,'nonzero_realized_failure':nonzero_failure,'realized_helly_failure':real_helly,
 'cut_clique_sizes':dict(sorted(Counter(map(len,inc.values())).items())),
 'nontrivial_cut_cliques':cliques,'euler_order_type_checks':replayed,'original_join_replays':crossed_replays}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('catalogue5','catalogue7','nontrivial_cut_cliques','realized_failure')},indent=2))
