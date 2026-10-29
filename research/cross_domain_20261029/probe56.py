"""Exact falsification of coarse topological and parse-count summaries."""
import runpy,pathlib,itertools,math,json,collections
D=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(D/'noncrossing_components_20261029/check_components.py'))
patterns,canon,win,crosses,closure,blocks=(d[k] for k in ['patterns','canon','win','crosses','closure','blocks'])
local=list(patterns(5));rows=[]
def cycles(p):
 seen=set();k=0
 for i in range(len(p)):
  if i in seen:continue
  k+=1;j=i
  while j not in seen:seen.add(j);j=p[j]
 return k
def genus(p):
 n=len(p);s=list(range(n))
 for B in blocks(p):
  for a,b in zip(B,B[1:]+B[:1]):s[a]=b
 inv=[0]*n
 for a,b in enumerate(s):inv[b]=a
 return (n+1-len(blocks(p))-cycles([inv[(i+1)%n] for i in range(n)]))//2
for B in itertools.combinations(range(11),5):
 C=tuple(i for i in range(11) if i not in B);p=canon(tuple(0 if i in B else 1 for i in range(11)))
 if closure(p)!=(0,)*11:continue
 c=0;cert=0
 for u,v in itertools.product(local,list(patterns(6))):
  q=[0]*11
  for i,a in zip(B,u):q[i]=a
  for i,a in zip(C,v):q[i]=a+5
  q=canon(q);ku=len(set(u));kv=len(set(v))
  mu=(-1)**(ku+kv-2)*math.factorial(ku-1)*math.factorial(kv-1)
  c+=mu*win(q)
  if all(len(b) in (2,3) for b in blocks(q)) and crosses(q) is None:cert+=1
 rows.append({'p':p,'coefficient':c,'genus':genus(p),'certificates':cert})
def collisions(key):
 bins=collections.defaultdict(dict)
 for r in rows:bins[str(key(r))].setdefault(r['coefficient'],r)
 return [{'feature':k,'witnesses':list(v.values())} for k,v in bins.items() if len(v)>1]
def entropy(key):
 bins=collections.defaultdict(collections.Counter)
 for r in rows:bins[str(key(r))][r['coefficient']]+=1
 return sum(sum(v.values())/len(rows)*(-sum(x/sum(v.values())*math.log2(x/sum(v.values())) for x in v.values())) for v in bins.values())
out={'status':'VERIFIED-COMP','scope':'every connected partition of type (5,6) at n=11','method':'partition-lattice Mobius inversion of independent raw maximal-run indicator','rows':rows,'histogram':dict(collections.Counter(r['coefficient'] for r in rows)),'collisions_graph':collisions(lambda r:'K2'),'collisions_genus':collisions(lambda r:r['genus']),'collisions_certificates':collisions(lambda r:r['certificates']),'entropy_bits':{k:entropy(f) for k,f in [('graph',lambda r:'K2'),('genus',lambda r:r['genus']),('certificates',lambda r:r['certificates']),('genus_and_certificates',lambda r:(r['genus'],r['certificates']))]}}
pathlib.Path(__file__).with_name('results56.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
