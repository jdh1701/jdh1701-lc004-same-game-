"""Independent small-pattern check of the universal classwise cut family."""
from pathlib import Path
import sys,json,itertools as it
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research'))
from certificate_join_count import patterns,join_coefficients,certificate_constraints,join

def le(a,b):
    return all(a[i]!=a[j] or b[i]==b[j] for i in range(len(a)) for j in range(i))
def canon(word):
    names={};return tuple(names.setdefault(a,len(names)) for a in word)
def cuts(p):
    out=set()
    for a in set(p):
        g=[i for i,x in enumerate(p) if x==a]
        for mask in range((1<<(len(g)-1))-1):
            side={g[0]}|{i for j,i in enumerate(g[1:]) if mask>>j&1}
            out.add(canon((x,(i in side) if x==a else False) for i,x in enumerate(p)))
    return sorted(out)
def faces(fs):
    F=set()
    for f in fs:
        for k in range(len(f)+1):F.update(it.combinations(sorted(f),k))
    return F
rows=[];refinements=0
for n in range(8):
    ps=[p for p,_ in patterns(n)];weights,_=join_coefficients(n);cs=list(certificate_constraints(n))
    for p in ps:
        V=cuts(p);assert all(v!=p and le(v,p) for v in V)
        for r in ps:
            if r!=p and le(r,p):
                assert any(le(r,v) for v in V);refinements+=1
        gens=[c for c in cs if le(c,p)]
        fs=[frozenset(j for j,v in enumerate(V) if le(c,v)) for c in gens]
        val=sum((-1)**len(f) for f in faces(fs))
        assert val==weights.get(p,0),(p,val,weights.get(p,0))
        rows.append(dict(p=p,cuts=len(V),coefficient=val))
    print('PASS n',n,'patterns',len(ps),flush=True)
out=dict(status='VERIFIED-COMP',patterns=len(rows),proper_refinements_checked=refinements,rows=rows)
(HERE/'class_cut_check.json').write_text(json.dumps(out,indent=2)+'\n')
print('TOTAL',len(rows),'patterns',refinements,'proper refinements',flush=True)
