"""Usage: python minimal_five_kernel.py support10.tsv support15.tsv.
Inputs from signed_support.cpp at primary checkpoint 31a286a.
"""
import sys,csv,itertools,json
from collections import Counter

def canon(w):
 d={};return tuple(d.setdefault(a,len(d)) for a in w)
def closure(w):
 while True:
  edge=next(((w[i],w[j]) for i,j,k,l in itertools.combinations(range(len(w)),4)
      if w[i]==w[k] and w[j]==w[l] and w[i]!=w[j]),None)
  if edge is None:return w
  a,b=edge;w=canon(tuple(a if x==b else x for x in w))
out=[]
for path in sys.argv[1:]:
 dist=Counter();orbits=Counter();seen=set();n=None
 for r in csv.DictReader(open(path),delimiter='\t'):
  w=canon(tuple(map(int,r['pattern'].split(','))));c=int(r['coefficient']);n=len(w)
  if set(Counter(w).values())!={5} or len(set(closure(w)))!=1:continue
  dist[c]+=1
  orb={canon(w[i:]+w[:i]) for i in range(n)}
  if w not in seen:orbits[(len(orb),c)]+=1;seen.update(orb)
 out.append({'n':n,'j':n//5,'connected_weight_distribution':dict(dist),'weighted_sum':sum(c*count for c,count in dist.items()),'cyclic_orbits':[{'size':s,'coefficient':c,'count':v} for (s,c),v in sorted(orbits.items())]})
print(json.dumps(out,indent=2))
