"""Exhaustive finite controls for closure fibers and additive class counts."""
import runpy, pathlib, itertools, json
base=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(base/'noncrossing_components_20261029/check_components.py'))
patterns,closure,blocks,canon,le=(d[k] for k in ['patterns','closure','blocks','canon','le'])
rows=[]
for n in range(8):
 ps=list(patterns(n));checks=0
 for pi in ps:
  if closure(pi)!=pi:continue
  bs=blocks(pi)
  fiber=[p for p in ps if closure(p)==pi]
  expected=1
  for b in bs:
   expected*=sum(closure(r)==(0,)*len(b) for r in patterns(len(b)))
  assert len(fiber)==expected
  for p in ps:
   if not le(p,pi):continue
   rs=[canon(tuple(p[i] for i in b)) for b in bs]
   assert (closure(p)==pi)==all(closure(r)==(0,)*len(r) for r in rs)
   assert len(set(p))==sum(len(set(r)) for r in rs)
   checks+=1
  assert len({tuple(canon(tuple(p[i] for i in b)) for b in bs) for p in fiber})==len(fiber)
 rows.append({'n':n,'checks':checks})
out={'status':'VERIFIED-COMP','rows':rows,'total':sum(r['checks'] for r in rows),'scope':'all patterns n=0..7; includes empty case; not a universal proof of class-count additivity'}
pathlib.Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
