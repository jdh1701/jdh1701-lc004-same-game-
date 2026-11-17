"""Distinguish proper-generator-join obstructions from actual signed cancellation."""
import json
import sys
import collections
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research'))
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from certificate_join_count import join,canonical
from verify_global_nc_bridge import nc_certificates
rows=json.loads(Path(__file__).with_name('results.json').read_text())['rows']
catalogue=nc_certificates(4,1)+nc_certificates(1,3)
hist=collections.Counter();witness=[]
for r in rows:
    if not r['connected']:continue
    p=tuple(r['pattern'])
    gens=[canonical(bs,11) for bs in catalogue if all(len({p[x] for x in b})==1 for b in bs)]
    q=tuple(range(11))
    for c in gens:q=join(q,c)
    hist[str((len(gens),r['coefficient'],q==p))]+=1
    if r['coefficient']==0 and q==p and len(witness)<3:witness.append(r)
proper=sum(n for key,n in hist.items() if key.endswith('False)'))
zero_full=sum(n for key,n in hist.items() if ', 0, True)' in key)
assert (proper,zero_full)==(385,44)
out=dict(status='VERIFIED-COMP',crossing_cases=451,proper_generator_join_cases=proper,
    zero_coefficient_despite_full_generator_join=zero_full,
    common_refinement_obstruction_histogram=dict(hist),zero_but_full_generator_join_examples=witness)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='zero_but_full_generator_join_examples'},indent=2))
