"""Polynomial recognition/evaluation on two proved coefficient strata.

all_five_coefficient: arbitrary all-five patterns, including disconnected ones.
universal_seven_coefficient: NCConnected (7,5,...,5) with a universal local
seven-certificate; returns None outside that proved domain, never a guess.

These algorithms rely on the paper run theorem plus the certified all-five
SCC law. They do not enumerate complete certificate assignments.
"""
from pathlib import Path
import sys
from collections import deque
from itertools import combinations
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import blocks,catalogue,crossing
C5=catalogue(5);C7=catalogue(7)

def normalize(p):
 names={};return tuple(names.setdefault(x,len(names)) for x in p)

def class_components(gs):
 adj=[set() for _ in gs]
 for i,j in combinations(range(len(gs)),2):
  if crossing(gs[i],gs[j]):adj[i].add(j);adj[j].add(i)
 todo=set(range(len(gs)));out=[]
 while todo:
  start=min(todo);seen={start};stack=[start]
  while stack:
   i=stack.pop()
   for j in adj[i]-seen:seen.add(j);stack.append(j)
  todo-=seen;out.append(seen)
 return out

def placed(g,c):return tuple(tuple(g[i] for i in b) for b in blocks(c))
def compatible(A,B):return not any(crossing(a,b) for a in A for b in B)

def connected_five_coefficient(p):
 gs=blocks(p);k=len(gs)
 if k==1:return -4
 candidates=[]
 for g in gs:
  edges=[frozenset((u,v)) for u,v in zip(g,g[1:]+g[:1]) if (u+1)%len(p)==v]
  if len(edges)!=2 or not edges[0].isdisjoint(edges[1]):return 0
  choices=[]
  for e in edges:
   choices.append(next(placed(g,c) for c in C5 if
     frozenset(next(b for b in placed(g,c) if len(b)==2))==e))
  candidates.append(choices)
 # A candidate and its coordinatewise complement must BOTH be certificates.
 # Every resulting symmetric binary relation is all, equality, inequality,
 # or empty. Therefore finding a separated pair is just XOR propagation.
 rel={};xor=[[] for _ in gs]
 for i,j in combinations(range(k),2):
  R=[[compatible(candidates[i][a],candidates[j][b]) for b in range(2)] for a in range(2)]
  rel[i,j]=R
  eq=R[0][0] and R[1][1];ne=R[0][1] and R[1][0]
  if not eq and not ne:return 0
  if eq!=ne:
   parity=int(ne);xor[i].append((j,parity));xor[j].append((i,parity))
 a=[None]*k
 for start in range(k):
  if a[start] is not None:continue
  a[start]=0;todo=deque([start])
  while todo:
   i=todo.popleft()
   for j,bit in xor[i]:
    need=a[i]^bit
    if a[j] is None:a[j]=need;todo.append(j)
    elif a[j]!=need:return 0
 def ok(i,j,x,y):return rel[i,j][x][y] if i<j else rel[j,i][y][x]
 # A valid separated pair is now available. The existing raw implication SCC
 # theorem excludes additional original local states as well as binary mixes.
 graph=[set() for _ in gs];reverse=[set() for _ in gs]
 for i in range(k):
  for j in range(k):
   if i!=j and not ok(i,j,1-a[i],a[j]):graph[i].add(j);reverse[j].add(i)
 def reaches_all(G):
  seen={0};todo=[0]
  while todo:
   i=todo.pop()
   for j in G[i]-seen:seen.add(j);todo.append(j)
  return len(seen)==k
 return -1 if reaches_all(graph) and reaches_all(reverse) else 0

def all_five_coefficient(p):
 p=normalize(p)
 if not p:return 1
 gs=blocks(p)
 if any(len(g)!=5 for g in gs):raise ValueError('all classes must have size five')
 value=1
 for component in class_components(gs):
  sub=normalize(tuple(x for x in p if x in component))
  value*=connected_five_coefficient(sub)
  if not value:return 0
 return value

def universal_seven_coefficient(p):
 p=normalize(p);gs=blocks(p)
 sevens=[i for i,g in enumerate(gs) if len(g)==7]
 if len(sevens)!=1 or any(len(g) not in (5,7) for g in gs) or len(gs)<2:return None
 if len(class_components(gs))!=1:return None
 h=sevens[0];H=gs[h];other=[g for i,g in enumerate(gs) if i!=h]
 if not any(all(not crossing(b,g) for b in placed(H,c) for g in other) for c in C7):return None
 result=0
 for u,v in zip(H,H[1:]+H[:1]):
  if (u+1)%len(p)!=v:continue
  rest=tuple(x for x in H if x not in (u,v))
  if any(crossing(rest,g) for g in other):
   result-=all_five_coefficient(tuple(x for i,x in enumerate(p) if i not in (u,v)))
 return result
