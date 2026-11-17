"""Construct the collapse from the paper proof, not by greedy facet search.

Inputs must satisfy the theorem's hypotheses; assertions deliberately expose
an invalid application. The returned steps can be checked on the original
facets without trusting the proof-construction algorithm.
"""
import itertools

def structural_collapse(choices):
    A = set(map(tuple, choices))
    assert len(A) >= 3
    j = len(next(iter(A)))
    D = [{a[i] for a in A} for i in range(j)]
    steps = []
    frozen = next((i for i in range(j) if len(D[i]) == 1), None)
    if frozen is not None:
        pivot = (frozen, next(iter(D[frozen])))
        return [(v, pivot) for v in sorted((i,x) for i in range(j) for x in D[i]) if v != pivot]

    def relation(i,k): return {(a[i], a[k]) for a in A}
    reps = []
    for i in range(j):
        rep = next((k for k in reps if len(relation(i,k)) == len(D[i]) == len(D[k])), None)
        if rep is None:
            reps.append(i)
        else:
            bij = dict(relation(i,rep))
            steps.extend(((i,x), (rep,bij[x])) for x in sorted(D[i]))
    assert len(reps) >= 2, 'One functional component; the small-edge hypothesis is essential'
    pivot = next(((i,x) for i in reps for x in sorted(D[i])
                  if all({y for u,y in relation(i,k) if u==x} == D[k]
                         for k in reps if k!=i)), None)
    assert pivot is not None, 'No sink in the value implication graph'
    i,x = pivot
    k = next((k for k in reps if k!=i and len(relation(i,k)) < len(D[i])*len(D[k])), None)
    assert k is not None, 'The reduced nonuniversal constraint graph is disconnected'
    for u in sorted(D[i]-{x}):
        ys = {y for z,y in relation(i,k) if z==u}
        assert len(ys)==1, 'Not a two-fan relation'
        steps.append(((i,u), (k,next(iter(ys)))))
    B = {tuple(a[k] for k in reps) for a in A}
    ii = reps.index(i)
    for b in B:
        replacement = list(b); replacement[ii]=x
        assert tuple(replacement) in B, 'Universal pair value failed to extend globally'
    steps.extend(((k,y), pivot) for k in reps if k!=i for y in sorted(D[k]))
    return steps

def verify(choices, steps):
    facets = {frozenset(enumerate(a)) for a in choices}
    for v,w in steps:
        assert v!=w and any(v in f for f in facets)
        assert all(w in f for f in facets if v in f), (v,w)
        reduced = {f-{v} for f in facets}
        facets = {f for f in reduced if not any(f<g for g in reduced)}
    assert len(set().union(*facets)) == 1

if __name__ == '__main__':
    import json,pathlib
    D=pathlib.Path(__file__).resolve().parent
    raw=json.loads((D/'classification.json').read_text())
    rows=[]
    for rs in raw['full_join_examples'].values():
        for r in rs:
            steps=structural_collapse(r['choices']);verify(r['choices'],steps)
            rows.append({'pattern':r['pattern'],'steps':steps})
    assert len(rows)==38
    (D/'structural_certificates.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
    print('VERIFIED-COMP: constructed and replayed 38 paper-proof collapse certificates')
