"""Structural proofs for all44 (5,6) full-join zeros.
Generate original certificates globally, then group by the actual five-class cut.
No local compatibility relation or existing coefficient value is used to build
or verify a cancellation certificate.
"""
from pathlib import Path
import json,sys,itertools as it,collections
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from verify_global_nc_bridge import nc_certificates
sys.path.insert(0,str(ROOT/'research'))
from certificate_join_count import canonical,join
allcs=nc_certificates(4,1)+nc_certificates(1,3)

def maxfs(fs):
    fs=set(fs);return {f for f in fs if not any(f<g for g in fs)}
def cuts(c,g):
    # Test every local cut directly on original-position equality relations.
    return frozenset(t for t in range((1<<(len(g)-1))-1)
        if all(c[g[u]]!=c[g[v]] or (1 if u==0 else (t>>(u-1))&1)==(1 if v==0 else (t>>(v-1))&1)
            for u in range(len(g)) for v in range(u)))
def common(fs):
    if not fs:return 'empty'
    s=set.intersection(*(set(f) for f in fs))
    return min(s) if s else None

def collapse(fs):
    fs=maxfs(fs);trace=[]
    while len(set().union(*fs))>1:
        pair=None
        for v in sorted(set().union(*fs)):
            d=set.intersection(*(set(f) for f in fs if v in f))-{v}
            if d:pair=v,min(d);break
        assert pair is not None,'projection did not strongly collapse'
        v,w=pair;assert all(w in f for f in fs if v in f)
        trace.append([v,w]);fs=maxfs(f-{v} for f in fs)
    return trace,fs

rows=json.loads((ROOT/'research/ten_attacks_20261030/topology.json').read_text())['rows']
proofs=[]
for old in rows:
    if old['profile']!=[5,6] or not old['full_join'] or old['coefficient']!=0:continue
    p=tuple(old['p']);groups=[tuple(i for i,a in enumerate(p) if a==k) for k in sorted(set(p))]
    G=next(g for g in groups if len(g)==5);H=next(g for g in groups if len(g)==6)
    cs=[canonical(bs,11) for bs in allcs if all(len({p[i] for i in b})==1 for b in bs)]
    rows={}
    for c in cs:
        left=cuts(c,G);assert len(left)==1
        row=next(iter(left));rows.setdefault(row,set()).add(cuts(c,H))
    rows={k:maxfs(fs) for k,fs in rows.items()};proj=maxfs(set().union(*rows.values()))
    dominant=next((k for k,fs in rows.items() if fs==proj and all(j==k or common(g) is not None for j,g in rows.items())),None)
    if dominant is not None:
        proof=dict(kind='dominant-row',dominant=dominant,partners={j:common(fs) for j,fs in rows.items() if j!=dominant})
    else:
        assert all(common(fs) is not None for fs in rows.values())
        trace,point=collapse(proj)
        proof=dict(kind='collapsible-projection',projection_trace=trace,point=[sorted(f) for f in point],partners={j:common(fs) for j,fs in rows.items()})
    # Original join polynomial is an independent algebraic verification.
    acc={}
    for c in cs:
        delta=collections.defaultdict(int);delta[c]+=1
        for q,v in acc.items():delta[join(q,c)]-=v
        for q,v in delta.items():
            acc[q]=acc.get(q,0)+v
            if not acc[q]:del acc[q]
    assert acc.get(p,0)==0
    proofs.append(dict(p=p,original_generators=cs,rows={k:[sorted(f) for f in fs] for k,fs in rows.items()},projection=[sorted(f) for f in proj],proof=proof))
assert len(proofs)==44
counts=collections.Counter(r['proof']['kind'] for r in proofs)
assert counts=={'dominant-row':33,'collapsible-projection':11}
out=dict(status='VERIFIED-COMP',original_catalogue_size=len(allcs),cases=len(proofs),mechanisms=dict(counts),proofs=proofs)
(HERE/'mixed_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(proofs),'original patterns; mechanisms',dict(counts),'global catalogue',len(allcs))
