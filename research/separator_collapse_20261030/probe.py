"""Exact two-class separator-complex experiment; no Lean proof claim."""
from functools import lru_cache
from itertools import combinations,product
from collections import Counter,defaultdict
from pathlib import Path
import json,time,argparse,heapq,hashlib
from math import comb

@lru_cache(None)
def local(n):
 if n==0:return ((),)
 out=[]
 for k in (2,3):
  for tail in combinations(range(1,n),k-1):
   root=(0,)+tail;ends=root+(n,)
   intervals=[range(ends[j]+1,ends[j+1]) for j in range(k)]
   for children in product(*(local(len(v)) for v in intervals)):
    blocks=[root]
    for points,cs in zip(intervals,children):
     blocks.extend(tuple(points[i] for i in b) for b in cs)
    out.append(tuple(sorted(blocks)))
 assert len(out)==len(set(out))
 return tuple(out)

def crossing(A,B):
 labels=[t for _,t in sorted([(x,0) for x in A]+[(x,1) for x in B])]
 return 1+sum(x!=y for x,y in zip(labels,labels[1:]))>=4

def labels(blocks,n):
 out=[0]*n
 for k,b in enumerate(blocks):
  for i in b:out[i]=k
 return tuple(out)

@lru_cache(None)
def join(p,q):
 parent=list(range(len(p)))
 def find(i):
  while i!=parent[i]:i,parent[i]=parent[i],parent[parent[i]]
  return i
 for w in (p,q):
  reps={}
  for i,v in enumerate(w):
   if v in reps:parent[find(i)]=find(reps[v])
   else:reps[v]=i
 names={};return tuple(names.setdefault(find(i),len(names)) for i in range(len(p)))

def cutfacet(blocks):
 ans=0
 for bits in range((1<<(len(blocks)-1))-1):
  side=sum(1<<x for x in blocks[0])
  for i,b in enumerate(blocks[1:]):
   if bits>>i&1:side|=sum(1<<x for x in b)
  ans|=1<<(side>>1)
 return ans

def faces(facets):
 out=set()
 for f in facets:
  s=f
  while True:
   out.add(s)
   if not s:break
   s=(s-1)&f
 return out

def coefficient(cs,a,b):
 acc={}
 for c in cs:
  delta=defaultdict(int);delta[c]+=1
  for old,w in acc.items():delta[join(old[0],c[0]),join(old[1],c[1])]-=w
  for k,w in delta.items():
   acc[k]=acc.get(k,0)+w
   if not acc[k]:del acc[k]
 return acc.get(((0,)*a,(0,)*b),0)

def fulljoin(cs,a,b):
 if not cs:return False
 x,y=tuple(range(a)),tuple(range(b))
 for p,q in cs:x,y=join(x,p),join(y,q)
 return x==(0,)*a and y==(0,)*b

def collapse(F):
 F=set(F);trace=[];cofaces={f:set() for f in F};queue=[]
 for t in F:
  bits=t
  while bits:
   bit=bits&-bits;bits-=bit;cofaces[t^bit].add(t)
 for s,ts in cofaces.items():
  if s and len(ts)==1:heapq.heappush(queue,(-s.bit_count(),-s,s))
 while queue and len(F)>2:
  _,_,s=heapq.heappop(queue)
  if s not in F or len(cofaces[s])!=1:continue
  t=next(iter(cofaces[s]));assert t in F and s.bit_count()+1==t.bit_count()
  for f in [s,t]:
   F.remove(f);bits=f
   while bits:
    bit=bits&-bits;bits-=bit;u=f^bit
    if u in F:
     cofaces[u].discard(f)
     if u and len(cofaces[u])==1:heapq.heappush(queue,(-u.bit_count(),-u,u))
   cofaces.pop(f)
  trace.append([s,t])
 return len(F)==2 and 0 in F,trace,F

def rank2(columns):
 pivots={}
 for c in columns:
  while c:
   p=c.bit_length()-1
   if p in pivots:c^=pivots[p]
   else:pivots[p]=c;break
 return len(pivots)

def homology(F):
 levels=defaultdict(list)
 for f in sorted(F):
  if f:levels[f.bit_count()-1].append(f)
 if not levels:return {}
 maxd=max(levels);ranks={0:0,maxd+1:0}
 for d in range(1,maxd+1):
  index={f:i for i,f in enumerate(levels[d-1])};cols=[]
  for f in levels[d]:
   col=0;bits=f
   while bits:
    bit=bits&-bits;bits-=bit;col^=1<<index[f^bit]
   cols.append(col)
  ranks[d]=rank2(cols)
 betti={d:len(levels[d])-ranks[d]-ranks[d+1]-(d==0) for d in range(maxd+1)}
 assert all(b>=0 for b in betti.values())
 assert sum((-1)**f.bit_count() for f in F)==-sum((-1)**d*b for d,b in betti.items())
 return {str(d):b for d,b in betti.items() if b}

@lru_cache(None)
def original(w):
 if not w:return ((),)
 out=[];n=len(w)
 for k in (2,3):
  for tail in combinations([i for i in range(1,n) if w[i]==w[0]],k-1):
   root=(0,)+tail;ends=root+(n,)
   intervals=[tuple(range(ends[j]+1,ends[j+1])) for j in range(k)]
   for children in product(*(original(tuple(w[i] for i in I)) for I in intervals)):
    blocks=[root]
    for I,cs in zip(intervals,children):blocks.extend(tuple(I[i] for i in B) for B in cs)
    out.append(tuple(sorted(blocks)))
 return tuple(out)

def run(a,b):
 start=time.monotonic();n=a+b;A=local(a);B=local(b)
 metadata={};hist=Counter();out=[];nonzero={};zero_certificates=[];join_checks=0;patterns=0;crossing_patterns=0;zero_full=0;collapsed=0;unknown=0
 for G in combinations(range(n),a):
  if a==b and 0 not in G:continue  # quotient the swap of equal-sized colors
  H=tuple(i for i in range(n) if i not in G);patterns+=1
  if not crossing(G,H):continue
  crossing_patterns+=1
  liftedA=[tuple(tuple(G[i] for i in block) for block in c) for c in A]
  liftedB=[tuple(tuple(H[i] for i in block) for block in c) for c in B]
  cs=[];facets=set();global_cs=set()
  for i,p in enumerate(liftedA):
   for j,q in enumerate(liftedB):
    if any(crossing(x,y) for x in p for y in q):continue
    cs.append((labels(A[i],a),labels(B[j],b)))
    facets.add(cutfacet(A[i])|(cutfacet(B[j])<<((1<<(a-1))-1)))
    global_cs.add(tuple(sorted(p+q)))
  w=tuple(0 if i in G else 1 for i in range(n))
  assert global_cs==set(original(w)),('independent catalogue',w)
  if not fulljoin(cs,a,b):
   hist['proper_join_zero']+=1;continue
  F=faces(facets);value=sum((-1)**s.bit_count() for s in F)
  if n<=12 or str(value) not in hist or join_checks<10:
   assert value==coefficient(cs,a,b),('join/Euler discrepancy',w)
   join_checks+=1
  hist[str(value)]+=1
  if value:
   nonzero.setdefault(str(value),dict(pattern=w,generators=len(cs),facets=sorted(facets),reduced_betti_mod2=homology(F)))
   continue
  zero_full+=1;ok,trace,residual=collapse(F)
  if ok:
   from independent import replay
   replay(F,trace)
   collapsed+=1
   zero_certificates.append(dict(pattern=w,faces=len(F),steps=len(trace),trace_sha256=hashlib.sha256(json.dumps(trace,separators=(",",":")).encode()).hexdigest()))
  else:
   betti=homology(residual)
   status='noncollapsible_by_nonzero_homology' if betti else 'greedy_stalled_acyclic_not_decided'
   unknown+=not bool(betti)
   out.append(dict(pattern=w,generators=len(cs),facets=sorted(facets),faces=len(F),status=status,
                   reduced_betti_mod2=betti,greedy_residual_faces=sorted(residual),trace=trace))
  if zero_full==1:metadata['first_zero_collapse']=dict(pattern=w,facets=sorted(facets),trace=trace,success=ok)
 assert patterns==comb(n,a)//(2 if a==b else 1)
 print(json.dumps(dict(profile=[a,b],patterns=patterns,crossing=crossing_patterns,local_catalogues=[len(A),len(B)],histogram=dict(hist),full_join_zeros=zero_full,collapsed=collapsed,stalled=len(out),undecided=unknown,seconds=round(time.monotonic()-start,3))),flush=True)
 return dict(profile=[a,b],patterns=patterns,crossing=crossing_patterns,local_catalogues=[len(A),len(B)],histogram=dict(hist),full_join_zeros=zero_full,collapsed=collapsed,stalled=out,zero_collapse_certificates=zero_certificates,nonzero_examples=nonzero,independent_join_checks=join_checks,metadata=metadata,seconds=time.monotonic()-start)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--profiles',default='5,6;5,7;6,7');p.add_argument('--output',default='results.json');args=p.parse_args()
 result=[run(*map(int,s.split(','))) for s in args.profiles.split(';')]
 Path(args.output).write_text(json.dumps({'status':'VERIFIED-COMP','profiles':result,'claims':'Finite exact catalogue, join and Euler checks; greedy failure alone never proves noncollapsibility'},indent=2)+'\n')
