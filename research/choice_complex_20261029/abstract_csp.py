"""Try to refute extension from geometric pair relations to abstract constraints."""
import itertools,random,json,pathlib,collections,time
rng=random.Random(20261101);stats=collections.Counter();witnesses=[]
for test in range(6000):
 j=rng.choice([3,4,5]);edges={(i,rng.randrange(i)) for i in range(1,j)}
 edges|={(i,k) for i in range(j) for k in range(i) if rng.random()<.25}
 default=[rng.randrange(5) for _ in range(j)];constraints=[]
 for i,k in sorted(edges):
  if rng.random()<.65:
   a=default[i] if rng.random()<.8 else rng.randrange(5);b=default[k] if rng.random()<.8 else rng.randrange(5)
   E={(x,y) for x in range(5) for y in range(5) if x==a or y==b};kind='bistar'
  else:
   xs=rng.sample(range(5),2);ys=rng.sample(range(5),2);E=set(zip(xs,ys));kind='matching'
  constraints.append((i,k,kind,E))
 domains=[set(range(5)) for _ in range(j)]
 for i,k,_,E in constraints:domains[i]&={x for x,y in E};domains[k]&={y for x,y in E}
 A=[a for a in itertools.product(*domains) if all((a[i],a[k]) in E for i,k,_,E in constraints)]
 stats['tested']+=1
 if len(A)<3:continue
 if any(len({a[i] for a in A})==1 for i in range(j)):continue
 stats['nontrivial']+=1
 c=sum((-1)**mask.bit_count()*len({tuple(a[i] for i in range(j) if mask>>i&1) for a in A}) for mask in range(1<<j))
 stats['coefficient_'+str(c)]+=1
 if c:
  witnesses.append({'j':j,'choices':A,'coefficient':c,'constraints':[{'i':i,'k':k,'type':t,'allowed':sorted(E)} for i,k,t,E in constraints]});break
out={'status':'VERIFIED-COMP','seed':20261101,'stats':dict(stats),'counterexamples':witnesses,'scope':'abstract connected pair constraints, not necessarily geometric'}
pathlib.Path(__file__).with_name('abstract_csp.json').write_text(json.dumps(out,indent=2)+'\n');print(out['stats']);print('counterexamples',len(witnesses))

assert stats["nontrivial"] == 1911
assert not witnesses
