"""Independent replay of stored strong-collapse certificates."""
import json,pathlib
D=pathlib.Path(__file__).resolve().parent
r=json.loads((D/'structure.json').read_text());source=json.loads((D/'classification.json').read_text());A={tuple(x['pattern']):x['choices'] for rs in source['full_join_examples'].values() for x in rs}
count=0
for x in r['full_join_cases']:
 facets={frozenset((i,v) for i,v in enumerate(a)) for a in A[tuple(x['pattern'])]}
 for v,w in x['steps']:
  v,w=tuple(v),tuple(w);assert v!=w
  assert any(v in f for f in facets)
  assert all(w in f for f in facets if v in f)
  fs={f-{v} for f in facets};facets={f for f in fs if not any(f<g for g in fs)}
 assert len(set().union(*facets))==1
 count+=1
assert count==38
print('VERIFIED-COMP: replayed',count,'collapse certificates')
