"""Known exhaustive n=10 controls from independent raw-game inversion."""
import runpy,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(D/'all_five_adversarial_20261029/probe.py'))
rows=json.loads((D/'cross_domain_20261029/results.json').read_text())['rows']
for r in rows:
 p=r['p'];groups=[tuple(i for i,x in enumerate(p) if x==c) for c in sorted(set(p))]
 aa,_=d['atoms'](groups);c,_=d['coefficient'](aa,2)
 projected=sum((-1)**mask.bit_count()*len({tuple(a[i] for i in range(2) if mask>>i&1) for a in aa}) for mask in range(4))
 assert c==projected==r['coefficient'],r
out={'status':'VERIFIED-COMP','independent_n10_controls':len(rows),'nonzero':sum(r['coefficient']!=0 for r in rows)}
(D/'all_five_adversarial_20261029/controls.json').write_text(json.dumps(out)+'\n');print(out)
