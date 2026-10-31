"""Adversarial control for support restriction; no random sampling."""
import itertools,json,pathlib

def connected(j,edges):
    seen={0}
    while True:
        more=seen|{v for u,v in edges if u in seen}|{u for u,v in edges if v in seen}
        if more==seen:return len(seen)==j
        seen=more

def graphs(A,ambient):
    j=len(ambient);D=[{a[i] for a in A} for i in range(j)]
    raw=[];supported=[];covered=[]
    for i,k in itertools.combinations(range(j),2):
        E={(a[i],a[k]) for a in A}
        if E!=set(itertools.product(ambient[i],ambient[k])):raw.append((i,k))
        if E!=set(itertools.product(D[i],D[k])):supported.append((i,k))
        if any(all(a[i]==p or a[k]==q for a in A) for p in D[i] for q in D[k]):covered.append((i,k))
    return D,raw,supported,covered

def projection_sum(A,j):
    return sum((-1)**mask.bit_count()*len({tuple(a[i] for i in range(j) if mask>>i&1) for a in A}) for mask in range(1<<j))

def face_sum(A,j):
    faces=set()
    for a in A:
        for mask in range(1<<j):faces.add(frozenset((i,a[i]) for i in range(j) if mask>>i&1))
    return sum((-1)**len(f) for f in faces)

def m(a,b,c):return tuple(y if y==z else x for x,y,z in zip(a,b,c))

controls=[]
for name,A in [('independent_binary_product',set(itertools.product(range(2),repeat=2))),
               ('two_independent_equalities',{(x,x,y,y) for x,y in itertools.product(range(2),repeat=2)})]:
    j=len(next(iter(A)));ambient=[set(range(3)) for _ in range(j)]
    D,raw,supported,covered=graphs(A,ambient)
    assert connected(j,raw) and not connected(j,supported)
    assert all(len(d)==2 for d in D)
    assert all(m(a,b,c) in A for a,b,c in itertools.product(A,repeat=3))
    E={(i,k):{(a[i],a[k]) for a in A} for i,k in itertools.combinations(range(j),2)}
    binary={a for a in itertools.product(*ambient) if all((a[i],a[k]) in e for (i,k),e in E.items())}
    assert binary==A
    p=projection_sum(A,j);f=face_sum(A,j);assert p==f==1
    assert not connected(j,covered)
    controls.append({'name':name,'choices':sorted(A),'ambient_domains':[sorted(d) for d in ambient],
                     'supported_domains':[sorted(d) for d in D],'raw_nonuniversal_edges':raw,
                     'supported_nonuniversal_edges':supported,'cover_edges':covered,
                     'majority_closed':True,'binary_determined':True,'alternating_sum':f})

D=pathlib.Path(__file__).resolve().parent
source=json.loads((D.parent/'choice_complex_20261029/classification.json').read_text())
positive=[]
for rows in source['full_join_examples'].values():
    for r in rows:
        A=set(map(tuple,r['choices']));j=len(next(iter(A)))
        domains,_,_,edges=graphs(A,[set(range(5)) for _ in range(j)])
        assert all(len(d)>=2 for d in domains) and connected(j,edges)
        positive.append({'n':r['n'],'atoms':len(A),'pattern':r['pattern'],'covered_edges':edges})
assert len(positive)==38
out={'negative_candidate_status':'KILLED','candidate':'support restriction preserves nonuniversal-relation connectedness without further hypotheses',
     'negative_controls':controls,'positive_status':'VERIFIED-COMP','positive_scope':'38 stored biased geometric examples; not exhaustive',
     'positive_covered_graphs':positive}
(D/'normalization_controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('VERIFIED-COMP: 2 normalization counterexamples; all 38 nonconstant geometric examples have connected cover graphs')

