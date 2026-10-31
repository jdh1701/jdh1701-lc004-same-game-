"""Exhaustive small abstract stress test of the proposed structural extension."""
import itertools,json,pathlib,collections
from structure import collapse
from eliminate import structural_collapse,verify
j=4;pairs=list(itertools.combinations(range(j),2));assignments=list(itertools.product(range(2),repeat=j))
relations=[set(itertools.product(range(2),repeat=2))]+[{(x,y) for x in range(2) for y in range(2) if x==a or y==b} for a,b in itertools.product(range(2),repeat=2)]+[{(0,0),(1,1)},{(0,1),(1,0)}]
masks=[[sum(1<<i for i,a in enumerate(assignments) if (a[u],a[v]) in E) for E in relations] for u,v in pairs]
seen={};stats=collections.Counter();bad=[]
for types in itertools.product(range(7),repeat=len(pairs)):
 reachable={0}
 while True:
  new=reachable|{v for (u,v),t in zip(pairs,types) if t and u in reachable}|{u for (u,v),t in zip(pairs,types) if t and v in reachable}
  if new==reachable:break
  reachable=new
 if len(reachable)!=j:continue
 S=(1<<len(assignments))-1
 for k,t in enumerate(types):S &= masks[k][t]
 stats['connected_presentations']+=1
 if S in seen:continue
 seen[S]=types;A=[a for i,a in enumerate(assignments) if S>>i&1]
 if len(A)<3 or any(len({a[k] for a in A})==1 for k in range(j)):continue
 stats['distinct_nontrivial_relations']+=1
 c=sum((-1)**T.bit_count()*len({tuple(a[k] for k in range(j) if T>>k&1) for a in A}) for T in range(1<<j))
 verify(A,structural_collapse(A))
 stats["paper_construction_verified"]+=1
 ok,steps=collapse(A)
 if not ok:stats['not_strongly_collapsible']+=1
 if c:bad.append({'choices':A,'coefficient':c,'edge_types':types})
out={'status':'VERIFIED-COMP','j':j,'presentations':7**len(pairs),'stats':dict(stats),'distinct_relations':len(seen),'counterexamples':bad}
pathlib.Path(__file__).with_name('boolean_exhaustive.json').write_text(json.dumps(out,indent=2)+'\n');print(out)

assert stats["distinct_nontrivial_relations"] == 2640
assert not bad
assert stats["not_strongly_collapsible"] == 0
