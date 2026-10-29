"""Exact raw-game check of the refinement-ideal identity, independent of Lean."""
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json,time

def canon(w):
 d={};return tuple(d.setdefault(a,len(d)) for a in w)
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

def patterns(n):
 def rec(w,k):
  if len(w)==n:yield w;return
  for a in range(k+1):yield from rec(w+(a,),max(k,a+1))
 yield from rec((),0)

def split(w,pair):return canon(tuple((a,i in pair) for i,a in enumerate(w)))

start=time.time();checks=0
for n in range(4,10):
 for p in patterns(n):
  for color,size in Counter(p).items():
   if size!=4:continue
   a,b,c,d=pos=[i for i,x in enumerate(p) if x==color]
   for refinement in patterns(4):
    r=list(p)
    for i,j in enumerate(pos):r[j]=max(p)+1+refinement[i]
    r=canon(tuple(r))
    lhs=int(win(r))-int(win(split(r,{c,d})))-int(win(split(r,{b,c})))
    gaps=[r[a+1:b],r[b+1:c],r[c+1:d],r[d+1:]+r[:a]]
    rhs=-int(len({r[i] for i in pos})==1 and all(win(canon(g)) for g in gaps))
    assert lhs==rhs,(p,r,pos,lhs,rhs)
    checks+=1
out={'checks':checks,'max_length':9,'A_refinements_per_case':15,'scope':'All upper equality patterns through n=9 and all partitions of each distinguished four-class; other classes unchanged. Universal Lean proof handles arbitrary refinements.','seconds':time.time()-start}
Path(__file__).with_name('refinement_python_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
