"""Seeded certificate-conditioned search; independent implementation, not exhaustive."""
import random,itertools,collections,json,pathlib,time
rng=random.Random(20261031)
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
def cross(A,B):
 last=None;runs=0
 for _,c in sorted([(x,0) for x in A]+[(x,1) for x in B]):
  if c!=last:runs+=1;last=c
 return runs>=4
def nc_certificate(a,b):
 if not a+b:return [],0
 k=rng.choice(([2] if a else [])+([3] if b else []));a-=k==2;b-=k==3
 counts=[[0,0] for _ in range(k)]
 for _ in range(a):counts[rng.randrange(k)][0]+=1
 for _ in range(b):counts[rng.randrange(k)][1]+=1
 out=[];root=[];pos=0
 for x,y in counts:
  root.append(pos);pos+=1
  cs,n=nc_certificate(x,y);out.extend(tuple(t+pos for t in c) for c in cs);pos+=n
 out.append(tuple(root));return out,pos
def connected(groups):
 g=[tuple(x) for x in groups]
 while len(g)>1:
  edge=next(((i,j) for i in range(len(g)) for j in range(i) if cross(g[i],g[j])),None)
  if edge is None:return False
  i,j=edge;g[j]=tuple(sorted(g[i]+g[j]));g.pop(i)
 return True
def atoms(groups):
 options=[]
 for G in groups:
  opts=[]
  for P in itertools.combinations(G,2):
   T=tuple(x for x in G if x not in P)
   if not cross(P,T):opts.append((P,T))
  options.append(opts)
 out=[]
 def rec(i,blocks,choices):
  if i==len(groups):out.append(tuple(choices));return
  for k,(P,T) in enumerate(options[i]):
   if any(cross(P,B) or cross(T,B) for B in blocks):continue
   rec(i+1,blocks+[P,T],choices+[k])
 rec(0,[],[]);return out,options
def coefficient(cs,j):
 acc={(-2,)*j:1};peak=1
 for a in cs:
  nxt=collections.defaultdict(int,acc)
  for s,v in acc.items():
   z=tuple(y if x==-2 else x if x==y else -1 for x,y in zip(s,a));nxt[z]-=v
  acc={s:v for s,v in nxt.items() if v};peak=max(peak,len(acc))
 return -acc.get((-1,)*j,0),peak
start=time.time();summaries=[];tested=[]
for j,attempts in [(2,200),(3,400),(4,600),(5,2000),(6,2000)]:
 seen=set();counts=collections.Counter();hist=collections.Counter();maxatoms=0;peak=0
 for _ in range(attempts):
  cs,n=nc_certificate(j,j);P=[x for x in cs if len(x)==2];T=[x for x in cs if len(x)==3];rng.shuffle(T)
  groups=[tuple(sorted(p+t)) for p,t in zip(P,T)];w=[0]*n
  for k,G in enumerate(groups):
   for i in G:w[i]=k
  w=canon(w)
  if w in seen:continue
  seen.add(w)
  if not connected(groups):continue
  aa,opts=atoms(groups);assert aa
  c,pk=coefficient(aa,j)
  projected=sum((-1)**mask.bit_count()*len({tuple(a[i] for i in range(j) if mask>>i&1) for a in aa}) for mask in range(1<<j))
  assert c==projected,(w,c,projected)
  peak=max(peak,pk);maxatoms=max(maxatoms,len(aa));counts[len(aa)]+=1;hist[c]+=1
  if len(aa)>=3:
   tested.append({'n':n,'pattern':w,'atoms':len(aa),'coefficient':c})
  if c and len(aa)!=2:print('COUNTEREXAMPLE',n,w,len(aa),c,flush=True)
 summaries.append({'n':5*j,'attempts':attempts,'unique_candidates':len(seen),'connected':sum(counts.values()),'atom_histogram':dict(counts),'coefficient_histogram':dict(hist),'max_atoms':maxatoms,'max_join_states':peak})
 print(summaries[-1],flush=True)
out={'status':'VERIFIED-COMP','seed':20261031,'sampling':'biased certificate-conditioned; no exhaustive or probabilistic guarantee','summaries':summaries,'three_plus_cases':tested,'counterexamples':[r for r in tested if r['coefficient']!=0],'seconds':time.time()-start}
pathlib.Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
