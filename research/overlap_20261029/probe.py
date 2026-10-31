"""Exact certificate-join probe for fixed-profile summary collisions."""
import runpy,pathlib,itertools,collections,json,random
D=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(D/'cross_domain_20261029/crosscheck.py'))
cert_parts,canon,join=(d[k] for k in ['cert_parts','canon','join'])
def crossed(p):
 return any(p[a]==p[c] and p[b]==p[e] and p[a]!=p[b] for a,b,c,e in itertools.combinations(range(len(p)),4))
def certificates(p):
 B=[tuple(i for i,x in enumerate(p) if x==c) for c in sorted(set(p))]
 out=[]
 for parts in itertools.product(*(cert_parts(b) for b in B)):
  q=[0]*len(p)
  for k,b in enumerate(sum(parts,())):
   for i in b:q[i]=k
  if not crossed(q):out.append(canon(q))
 return out
def calculate(p):
 cs=certificates(p);acc={tuple(range(len(p))):1};peak=1
 for q in cs:
  nxt=collections.defaultdict(int,acc)
  for r,v in acc.items():nxt[join(r,q)]-=v
  acc={r:v for r,v in nxt.items() if v};peak=max(peak,len(acc))
 degrees=[0]*len(cs);edges=0
 for i,j in itertools.combinations(range(len(cs)),2):
  if join(cs[i],cs[j])==p:edges+=1;degrees[i]+=1;degrees[j]+=1
 return {'p':p,'certificates':len(cs),'coefficient':-acc.get(p,0),'top_pairs':edges,'degree_sequence':sorted(degrees),'peak_join_states':peak}
rows=[]
for rest in itertools.combinations(range(1,12),5):
 B=(0,)+rest;p=tuple(0 if i in B else 1 for i in range(12))
 if not crossed(p):continue
 rows.append(calculate(p))
def collisions(key):
 groups=collections.defaultdict(dict)
 for r in rows:groups[str(key(r))].setdefault(r['coefficient'],r)
 return [{'feature':k,'witnesses':list(v.values())} for k,v in groups.items() if len(v)>1]
out={'status':'VERIFIED-COMP','scope':'all crossed (6,6) partitions of 12, labels canonical','rows':rows,'histogram':dict(collections.Counter(r['coefficient'] for r in rows)),'count_collisions':collisions(lambda r:r['certificates']),'pair_collisions':collisions(lambda r:(r['certificates'],r['top_pairs'])),'degree_collisions':collisions(lambda r:r['degree_sequence'])}
pathlib.Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
