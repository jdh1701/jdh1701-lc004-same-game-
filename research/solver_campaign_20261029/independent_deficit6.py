"""Bounded-deficit face-profile extraction, independent of bf_k.c.
Outputs are conditional on the enumerative face-profile theorem, not its proof.
Does not use diagonal formulas or claimed target counts as inputs.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
from math import factorial,comb,prod
from fractions import Fraction
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

@lru_cache(None)
def omega(target):
 r=len(target);out=Counter();seen=0
 def rec(w,counts):
  nonlocal seen
  seen+=1
  if all(c!=1 for c in counts) and win(canon(w)):out[counts]+=1
  for a in range(r):
   if counts[a]<target[a]:
    nxt=list(counts);nxt[a]+=1;rec(w+(a,),tuple(nxt))
 rec((),(0,)*r)
 return dict(out)

def coefficient_power(target,b):
 zero=(0,)*len(target);dp={zero:1}
 terms=omega(target)
 for _ in range(b):
  new=Counter()
  for a,x in dp.items():
   for t,y in terms.items():
    s=tuple(i+j for i,j in zip(a,t))
    if all(i<=j for i,j in zip(s,target)):new[s]+=x*y
  dp=dict(new)
 return dp.get(target,0)

def heavy_profiles(budget,minimum=4):
 yield ()
 for s in range(minimum,budget+3):
  for rest in heavy_profiles(budget-(s-2),s):yield (s,)+rest

def count(n,k):
 deficit=n-2*k;total=Fraction(0);ledger=[]
 for sizes in heavy_profiles(deficit):
  r=len(sizes);m3=deficit-sum(s-2 for s in sizes);m2=k-r-m3
  if m2<0:continue
  w=m2+m3;b=n-sum(sizes)-w+1
  aut=prod(factorial(c) for c in Counter(sizes).values())
  power=coefficient_power(sizes,b) if sizes else 1
  term=Fraction(factorial(n)*power,factorial(n-w)*factorial(m2)*factorial(m3)*b*aut)
  total+=term;ledger.append(dict(m2=m2,m3=m3,heavy=sizes,faces=b,omega_power_coefficient=power,contribution=str(term)))
 assert total.denominator==1
 return dict(n=n,k=k,value=int(total),profiles=ledger)
start=time.time()
result={'method':'exact bounded-deficit content DP plus face-profile formula','mathematical_dependency':'full enumerative face-profile theorem remains under audit; not an independent proof of that theorem','results':[count(n,k) for n,k in [(8,1),(10,2),(12,3),(14,4),(16,5),(18,6),(20,7)]],'seconds':time.time()-start}
ys=[Fraction(x['value'],comb(x['n'],x['k']-1)) for x in result['results']]
predicted=sum((-1)**(6-i)*comb(6,i-1)*ys[i-1] for i in range(1,7))
result['degree5_holdout']={'fitted_k':list(range(1,7)),'held_out_k':7,'predicted_R6':str(predicted),'actual_R6':str(ys[6]),'difference':str(ys[6]-predicted),'qualification':'conditional on the face-profile enumeration formula'}
Path(__file__).with_name('independent_deficit6_results.json').write_text(json.dumps(result,indent=2)+'\n')
print([(x['n'],x['k'],x['value']) for x in result['results']],flush=True)
