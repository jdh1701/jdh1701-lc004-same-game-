"""Independent raw-deletion Mobius and facet-nerve topology checks."""
from functools import lru_cache
from itertools import combinations,product
from math import factorial
from collections import Counter
from pathlib import Path
import json
from probe import faces,homology,collapse

@lru_cache(None)
def partitions(points):
 if not points:return ((),)
 a=points[0];out=[]
 for k in range(2,len(points)+1):
  for tail in combinations(points[1:],k-1):
   block=(a,)+tail;rest=tuple(i for i in points if i not in block)
   for bs in partitions(rest):out.append((block,)+bs)
 return tuple(out)

def canon(w):
 names={};return tuple(names.setdefault(x,len(names)) for x in w)

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

def mobius(word):
 G=[i for i,a in enumerate(word) if a==0];H=[i for i,a in enumerate(word) if a==1]
 value=0;cases=0
 for A,B in product(partitions(tuple(G)),partitions(tuple(H))):
  w=[0]*len(word)
  for label,block in enumerate(A+B):
   for i in block:w[i]=label
  mu=(-1)**(len(A)+len(B)-2)*factorial(len(A)-1)*factorial(len(B)-1)
  value+=mu*win(canon(w));cases+=1
 return value,cases

def nerve(facets):
 vertices=0
 for f in facets:vertices|=f
 covers=[]
 while vertices:
  bit=vertices&-vertices;vertices-=bit
  covers.append(sum(1<<i for i,f in enumerate(facets) if f&bit))
 assert max((f.bit_count() for f in covers),default=0)<=18,'Nerve expansion resource bound'
 return faces(covers)

def replay(F,steps):
 F=set(F);incidence={}
 for f in F:
  bits=f
  while bits:
   bit=bits&-bits;bits-=bit;incidence.setdefault(bit,set()).add(f)
 for s,t in steps:
  assert s and s in F and t in F and s&t==s and t.bit_count()==s.bit_count()+1
  bits=s;lists=[]
  while bits:
   bit=bits&-bits;bits-=bit;lists.append(incidence[bit])
  lists.sort(key=len);cofaces=set(lists[0])
  for z in lists[1:]:cofaces.intersection_update(z)
  assert cofaces=={s,t},'Pair is not a free-face elementary collapse'
  for f in [s,t]:
   F.remove(f);bits=f
   while bits:
    bit=bits&-bits;bits-=bit;incidence[bit].remove(f)
 assert len(F)==2 and 0 in F

def main():
 root=Path(__file__).resolve().parent
 results=json.loads((root/'census.json').read_text())['profiles']
 out=[]
 for row in results:
  for value,example in row['nonzero_examples'].items():
   v,n=mobius(tuple(example['pattern']));assert v==int(value)
   F=faces(example['facets']);N=nerve(example['facets'])
   assert homology(N)==homology(F)==example['reduced_betti_mod2']
   out.append(dict(profile=row['profile'],coefficient=v,refinements_checked=n,
                   separator_faces=len(F),nerve_faces=len(N),betti=homology(N)))
  e=row['metadata']['first_zero_collapse'];assert e['success']
  replay(faces(e['facets']),e['trace'])
 # Negative control: circle plus isolated point has Euler zero but is not acyclic.
 F=faces([3,6,5,8]);assert sum((-1)**s.bit_count() for s in F)==0
 assert homology(F)=={'0':1,'1':1};assert not collapse(F)[0]
 # Positive cone control; its collapse must replay by the independent coface test.
 F=faces([3|16,6|16,5|16]);ok,steps,_=collapse(F);assert ok;replay(F,steps)
 (root/'independent-results.json').write_text(json.dumps(dict(status='VERIFIED-COMP',checks=out,
   controls='Circle-plus-point negative and cone positive; stored collapse traces replayed',
   method='Raw maximal-run deletion and full no-singleton refinement Mobius sum; dual facet-nerve GF2 homology'),indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
