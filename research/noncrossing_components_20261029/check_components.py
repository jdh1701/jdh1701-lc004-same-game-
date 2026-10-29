"""Independent exact finite controls for closure, fibers and game factorization."""
from collections import Counter,defaultdict
from functools import lru_cache
from pathlib import Path
import itertools,json,time

def canon(w):
 d={};return tuple(d.setdefault(a,len(d)) for a in w)
def patterns(n):
 def rec(w,k):
  if len(w)==n:yield w;return
  for a in range(k+1):yield from rec(w+(a,),max(k,a+1))
 yield from rec((),0)
def le(p,q):return all(q[i]==q[p.index(a)] for i,a in enumerate(p))
def crosses(p):
 return next(((p[a],p[b]) for a,b,c,d in itertools.combinations(range(len(p)),4)
  if p[a]==p[c] and p[b]==p[d] and p[a]!=p[b]),None)
def closure(p):
 while True:
  edge=crosses(p)
  if edge is None:return p
  a,b=edge;p=canon(tuple(a if i==b else i for i in p))
@lru_cache(None)
def win(w):
 if not w:return True
 i=0
 while i<len(w):
  j=i+1
  while j<len(w) and w[j]==w[i]:j+=1
  if j-i>=2 and win(canon(w[:i]+w[j:])):return True
  i=j
 return False

def blocks(p):return [tuple(i for i,a in enumerate(p) if a==b) for b in set(p)]
start=time.time();coeff={0:{():1}};rows=[]
for n in range(1,8):
 pats=list(patterns(n));nc=[p for p in pats if crosses(p) is None]
 coeff[n]={}
 for p in sorted(pats,key=lambda p:-len(set(p))):
  coeff[n][p]=int(win(p))-sum(c for q,c in coeff[n].items() if c and le(q,p))
 pushed=defaultdict(int)
 for p in pats:
  cl=closure(p);assert le(p,cl) and closure(cl)==cl
  assert all(le(cl,q) for q in nc if le(p,q))
  weight=(-1)**len(set(p))*(1+sum(len(b)**2 for b in blocks(p)))
  pushed[cl]+=weight
 checks=0
 for pi in nc:
  refined=[p for p in pats if le(p,pi)]
  expected=1
  for b in blocks(pi):expected*=len(list(patterns(len(b))))
  assert len(refined)==expected
  lower=sum((-1)**len(set(p))*(1+sum(len(b)**2 for b in blocks(p))) for p in refined)
  assert lower==sum(c for q,c in pushed.items() if le(q,pi))
  for p in refined:
   restrictions=[canon(tuple(p[i] for i in b)) for b in blocks(pi)]
   assert win(p)==all(win(q) for q in restrictions)
   value=1
   for q in restrictions:value*=coeff[len(q)][q]
   assert coeff[n][p]==value,(p,pi,coeff[n][p],value)
   checks+=1
 rows.append({'n':n,'patterns':len(pats),'noncrossing':len(nc),'region_factorization_checks':checks,'nonzero_coefficients':sum(c!=0 for c in coeff[n].values())})
out={'rows':rows,'seconds':time.time()-start,'arithmetic':'exact Python integers','range':'all set partitions through n=7; all refinements of every noncrossing partition'}
Path(__file__).with_name('component_results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
