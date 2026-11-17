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
