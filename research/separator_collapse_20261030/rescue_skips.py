"""Resolve the exact PR38 generator-budget skips using sparse facet reductions.
Expand faces only after certified reduction, within an explicit bound.
No inference from timeout or stalled collapse.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json,time,hashlib,gzip
from probe import local,crossing,cutfacet,original,labels,join,faces,collapse,homology
from independent import replay as replay_elementary

ROOT=Path(__file__).resolve().parent

def normalize_certified(inputs):
 inputs=set(inputs);out=[];incidence={};cover=[]
 for f in sorted(inputs,key=lambda x:(-x.bit_count(),-x)):
  bits=f;candidate=None
  while bits:
   v=bits&-bits;bits-=v
   candidate=incidence.get(v,0) if candidate is None else candidate&incidence.get(v,0)
   if not candidate:break
  if candidate:
   j=(candidate&-candidate).bit_length()-1
   assert f&out[j]==f
   cover.append((f,j));continue
  if not f and out:
   cover.append((f,0));continue
  j=len(out);out.append(f);cover.append((f,j));bits=f
  while bits:
   v=bits&-bits;bits-=v;incidence[v]=incidence.get(v,0)|(1<<j)
 # Verify preservation independently of the search index:
 # every input is covered, every output was an input.
 assert set(out)<=inputs
 assert {f for f,j in cover}==inputs
 assert all(f&out[j]==f for f,j in cover)
 return tuple(out)

def strong(facets):
 facets=normalize_certified(facets);trace=[]
 while facets:
  common={}
  for f in facets:
   bits=f
   while bits:
    v=bits&-bits;bits-=v;common[v]=common.get(v,f)&f
  pair=next(((v,(s&~v)&-(s&~v)) for v,s in sorted(common.items()) if s&~v),None)
  if pair is None:break
  v,w=pair
  assert v!=w and any(f&v for f in facets)
  assert all(f&w for f in facets if f&v)
  trace.append([v.bit_length()-1,w.bit_length()-1])
  facets=normalize_certified(f&~v for f in facets)
 return facets,trace

def replay(facets,trace):
 fs=normalize_certified(facets)
 for vi,wi in trace:
  v,w=1<<vi,1<<wi
  assert v!=w and any(f&v for f in fs)
  assert all(f&w for f in fs if f&v)
  fs=normalize_certified(f&~v for f in fs)
 return fs

def reconstruct(p):
 groups=[tuple(i for i,x in enumerate(p) if x==a) for a in sorted(set(p))]
 assert len(groups)==2
 A,B=map(lambda g:local(len(g)),groups)
 liftedA=[tuple(tuple(groups[0][i] for i in b) for b in c) for c in A]
 liftedB=[tuple(tuple(groups[1][i] for i in b) for b in c) for c in B]
 certificates=set();facets=set();offset=(1<<(len(groups[0])-1))-1
 for i,bs in enumerate(liftedA):
  for j,cs in enumerate(liftedB):
   if any(crossing(b,c) for b in bs for c in cs):continue
   certificates.add(tuple(sorted(bs+cs)))
   facets.add(cutfacet(A[i])|(cutfacet(B[j])<<offset))
 # A separate first-position interval oracle checks the complete generator set.
 assert certificates==set(original(tuple(p)))
 original.cache_clear()
 full=tuple(range(len(p)))
 for c in certificates:full=join(full,labels(c,len(p)))
 assert full==tuple(p), "Full generator join must be rechecked"
 return certificates,facets

def decision(facets):
 deadline=time.monotonic()+30;states=0
 @lru_cache(None)
 def beta(fs):
  nonlocal states
  states+=1
  if states>100000 or time.monotonic()>deadline:raise RuntimeError('explicit decision budget')
  if not fs:return 0
  if fs==(0,):return 1
  if len(fs)==1:return 0
  intersection=fs[0]
  union=0
  for f in fs:intersection&=f;union|=f
  if intersection:return 0
  # Highest-incidence vertex reduces both branches.
  vertices=[]
  while union:
   v=union&-union;union-=v;vertices.append(v)
  v=max(vertices,key=lambda b:sum(bool(f&b) for f in fs))
  deletion=normalize_certified(f&~v for f in fs)
  link=normalize_certified(f&~v for f in fs if f&v)
  return beta(deletion)-beta(link)
 value=beta(normalize_certified(facets))
 return value,states

def main():
 source=json.loads((ROOT/'skipped-inputs.json').read_text());rows=[]
 for index,input in enumerate(source['rows']):
  start=time.monotonic();p=tuple(input['p']);cs,facets=reconstruct(p)
  assert len(cs)==input['generators']
  reduced,trace=strong(facets)
  replayed=replay(facets,trace);assert replayed==reduced
  vertices=0
  for f in reduced:vertices|=f
  if vertices.bit_count()==1:
   value=0;states=0;status='zero-with-replayed-strong-collapse'
  else:
   try:value,states=decision(reduced);status='coefficient-resolved-collapse-not-asserted'
   except RuntimeError:value=None;states=None;status='explicit-decision-budget-skip'
  elementary=[];betti=None;vertex_map=[];face_value=None
  universe=vertices;mapping={}
  while universe:
   bit=universe&-universe;universe-=bit;mapping[bit]=1<<len(mapping);vertex_map.append(bit.bit_length()-1)
  def compact(f):
   result=0
   for old,new in mapping.items():
    if f&old:result|=new
   return result
  compact_facets=tuple(compact(f) for f in reduced)
  assert all(sum(1<<vertex_map[i] for i in range(len(vertex_map)) if compact(f)>>i&1)==f for f in reduced)
  upper=sum(1<<f.bit_count() for f in compact_facets)
  if value is not None and upper<=300000:
   face_value=sum((-1)**f.bit_count() for f in faces(compact_facets));assert face_value==value

  if value==0 and vertices.bit_count()!=1:
   if upper<=300000:
    F=faces(compact_facets);ok,elementary,residual=collapse(F)
    if ok:
     replay_elementary(F,elementary);status='zero-with-replayed-elementary-collapse'
    else:
     betti=homology(residual);status='zero-with-nonzero-homology' if betti else 'zero-collapse-undecided'
   else:status='zero-collapse-explicit-face-budget'
  row=dict(pattern=p,profile=input['profile'],generators=len(cs),source_skip=input['status'],
   status=status,coefficient=value,original_facets_count=len(facets),original_facets_sha256=hashlib.sha256(json.dumps(sorted(facets),separators=(",",":")).encode()).hexdigest(),strong_trace=trace,elementary_trace=elementary,elementary_vertex_map=vertex_map,direct_face_sum=face_value,reduced_betti_mod2=betti,
   strong_core_facets=list(reduced),strong_core_vertices=vertices.bit_count(),final_vertices=1 if value==0 and "replayed" in status else vertices.bit_count(),decision_states=states,
   seconds=round(time.monotonic()-start,4))
  rows.append(row);print(index,len(cs),status,value,row['seconds'],flush=True)
 result=dict(source_commit=source['source_commit'],archive_blob=source['archive_blob'],
  status='VERIFIED-COMP',patterns=len(rows),histogram=dict(Counter(r['status'] for r in rows)),rows=rows,
  assurance='Full original-generator comparisons and independently checked domination conditions; no Lean instantiation for individual patterns')
 assert len(rows)==32 and len({tuple(r['pattern']) for r in rows})==32
 assert result['histogram']=={'zero-with-replayed-elementary-collapse':17,
  'zero-with-replayed-strong-collapse':9,'coefficient-resolved-collapse-not-asserted':6}
 assert all(r['direct_face_sum']==r['coefficient'] for r in rows)
 assert Counter(r['coefficient'] for r in rows)==Counter({0:26,8:2,10:2,-4:2})
 archive=ROOT/'rescued-results.json.gz'
 def untimed(x):
  if isinstance(x,dict):return {k:untimed(v) for k,v in x.items() if k!='seconds'}
  if isinstance(x,list):return [untimed(v) for v in x]
  return x
 if archive.exists():
  assert untimed(result)==json.loads(gzip.decompress(archive.read_bytes())), 'Committed receipt differs'
 (ROOT/'rescued-results.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
