"""Exact hypergraph partition functions for certificate obstructions."""
import pathlib,runpy,json,itertools,functools
D=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(D/'overlap_20261029/probe.py'));certificates,join=(d[k] for k in ['certificates','join'])
witnesses=[tuple(w['pattern']) for w in json.loads((D/'overlap_20261029/higher67.json').read_text())['pair_graph_mismatches']]
r=json.loads((D/'overlap_20261029/results.json').read_text())['count_collisions'][0]['witnesses'][0];witnesses.append(tuple(r['p']))
rows=[]
for p in witnesses:
 cs=certificates(p);m=len(cs);edges=[];direct=[0]*(m+1)
 for mask in sorted(range(1<<m),key=int.bit_count):
  q=tuple(range(len(p)))
  for i,c in enumerate(cs):
   if mask>>i&1:q=join(q,c)
  if q==p:
   if not any(mask&e==e for e in edges):edges.append(mask)
  else:direct[mask.bit_count()]+=1
 def normalize(es):
  out=[]
  for e in sorted(set(es),key=int.bit_count):
   if not any(e&f==f for f in out):out.append(e)
  return tuple(sorted(out))
 @functools.lru_cache(None)
 def Z(V,E):
  if 0 in E:return (0,)
  if not V:return (1,)
  v=V&-V;W=V^v
  a=Z(W,normalize(e for e in E if not e&v))
  b=Z(W,normalize(e&~v for e in E))
  out=[0]*max(len(a),len(b)+1)
  for i,x in enumerate(a):out[i]+=x
  for i,x in enumerate(b):out[i+1]+=x
  return tuple(out)
 poly=Z((1<<m)-1,normalize(edges));poly=list(poly)+[0]*(len(direct)-len(poly));assert poly==direct
 value=sum((-1)**k*x for k,x in enumerate(poly))
 rows.append({'pattern':p,'certificates':m,'minimal_generator_sizes':sorted(e.bit_count() for e in edges),'partition_polynomial':poly,'Z_at_minus_one':value,'memoized_recursion_states':Z.cache_info().currsize,'subsets_used_to_construct_hypergraph':1<<m})
# A concrete obstruction to order-independent stabilization.
@functools.lru_cache(None)
def terminals(w):
 out=set();i=0
 while i<len(w):
  j=i+1
  while j<len(w) and w[j]==w[i]:j+=1
  if j-i>=2:out.update(terminals(w[:i]+w[j:]))
  i=j
 return frozenset(out or {w})
nonconfluent=None
for n in range(2,11):
 for w in itertools.product(range(2),repeat=n):
  t=terminals(w)
  if () in t and len(t)>1:nonconfluent={'word':w,'terminal_words':sorted(t)};break
 if nonconfluent:break
assert [r['Z_at_minus_one'] for r in rows]==[2,2,0]
assert nonconfluent=={'word':(0,0,1,1,0),'terminal_words':[(),(0,)]}
out={'status':'VERIFIED-COMP','hypergraph_examples':rows,'nonconfluent_game_example':nonconfluent,'scope':'finite witnesses; constructing hyperedges still enumerates subsets; no global speedup claimed'}
(D/'physics_audit_20261029/results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
