"""Independent bit-mask facets and original joins for one six-point class."""
import json
import itertools as it
import collections
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research'))
from certificate_join_count import join
cats=json.loads(Path(__file__).with_name('catalogues.json').read_text())['6']
facets=[]
for c in cats:
    facet=[]
    for t in range(31):
        bits=[True]+[bool(t>>i&1) for i in range(5)]
        if all(c[u]!=c[v] or bits[u]==bits[v] for u,v in it.product(range(6),repeat=2)):
            facet.append(t)
    facets.append(facet)
assert [len(f) for f in facets]==[1,1,3,3,3,1,3,3]
faces={tuple(f[i] for i in range(len(f)) if mask>>i&1) for f in facets for mask in range(1<<len(f))}
hist=collections.Counter(map(len,faces));value=sum((-1)**len(f) for f in faces)
assert dict(hist)=={0:1,1:12,2:15,3:5} and value==-1
coeff={}
for c in cats:
    c=tuple(c);new=dict(coeff);new[c]=new.get(c,0)+1
    for q,w in coeff.items():
        j=join(q,c);new[j]=new.get(j,0)-w
    coeff={q:w for q,w in new.items() if w}
assert coeff.get((0,)*6,0)==value
out=dict(status='VERIFIED-COMP',cuts=31,certificate_facets=facets,
         face_histogram={str(k):hist[k] for k in sorted(hist)},
         alternating_sum=value,original_partition_join_coefficient=coeff[(0,)*6])
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
