# Independent topology checks; SageMath 10.10 image pinned in CI.
import json
from pathlib import Path
rows=json.loads(Path('research/choice_complex_20261029/sage_fixtures.json').read_text())
checks=[]
for r in rows:
    facets=[[(i,int(v)) for i,v in enumerate(a)] for a in r['choices']]
    K=SimplicialComplex(facets)
    assert K.euler_characteristic()==1
    hom=K.homology(base_ring=QQ)
    assert all(H.dimension()==0 for H in hom.values())
    checks.append({'n':int(r['n']),'atoms':int(r['atoms']),'euler':int(K.euler_characteristic()),'reduced_rational_homology':'zero'})
# Nontrivial control: two disjoint facets have reduced H_0 of dimension one.
C=SimplicialComplex([[(0,0),(1,0)],[(0,1),(1,1)]])
assert C.euler_characteristic()==2
assert C.homology(base_ring=QQ)[0].dimension()==1
print(json.dumps({'sage_version':version(),'status':'VERIFIED-COMP','checks':len(checks),'control':'two components confirmed','rows':checks}))
