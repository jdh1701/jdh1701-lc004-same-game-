"""Exact five-class elimination; derived from exclusive marked separators."""
from fast_complex import *
import json,time,collections
HERE=Path(__file__).resolve().parent;OLD=ROOT/'research/ten_attacks_20261030'
start=time.time();rows=[];mixed=collections.Counter();examples={}
inputs={}
for name in ('topology','holdout','deep_holdout'):
 for r in json.loads((OLD/(name+'.json')).read_text())['rows']:
  if 'coefficient' in r and 5 in map(len,blocks(tuple(r['p']))):inputs[tuple(r['p'])]=r['coefficient']
for p,expected in sorted(inputs.items()):
 d=encode(p)
 for cls,g in enumerate(blocks(p)):
  if len(g)!=5:continue
  marked=[v for v,label in enumerate(d['labels']) if label[0]==cls];M=sum(1<<v for v in marked)
  assert all((f&M).bit_count()==1 for f in d['facets'])
  rowfacets={v:maximal(f&~M for f in d['facets'] if f>>v&1) for v in marked}
  projected=maximal(f&~M for f in d['facets'])
  basevalue=euler(projected);values={v:euler(fs) for v,fs in rowfacets.items()}
  value=basevalue-sum(values.values());assert value==expected,(p,cls,value,expected)
  dominators=[v for v,fs in rowfacets.items() if fs==projected and all(z==v or values[z]==0 for z in values)]
  r=dict(p=p,selected_class=cls,coefficient=value,projection_value=basevalue,row_values=sorted(values.values()),dominating_row_cancellation=bool(dominators),full_join=d['full_join'])
  rows.append(r)
  if sorted(map(len,blocks(p)))==[5,6] and d['full_join']:
   sig=(len(d['choices']),value,basevalue,tuple(sorted(values.values())),bool(dominators));mixed[str(sig)]+=1;examples.setdefault(str(sig),p)
out=dict(status='VERIFIED-COMP',distinct_patterns=len(inputs),elimination_checks=len(rows),mixed_full_join_signatures=dict(mixed),mixed_examples=examples,rows=rows,seconds=time.time()-start)
(HERE/'fibers.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(inputs),'patterns',len(rows),'eliminations','seconds',time.time()-start,flush=True)
print(json.dumps(dict(mixed),indent=2),flush=True)
