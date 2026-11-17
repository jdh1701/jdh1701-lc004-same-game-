"""Exhaust every two-class (5,6) interleaving via explicit local NC catalogues.
Compare relation geometry with original position-partition signed joins.
"""
import itertools as it
import json
import collections
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research'))
sys.path.insert(0,str(ROOT/'research/five_bridge_20261029'))
from verify_global_nc_bridge import nc_certificates
from certificate_join_count import canonical,join
cats=json.loads(Path(__file__).with_name('catalogues.json').read_text())

def crossing(a,b):
    return any(u<x<v<y or x<u<y<v for u,v in it.combinations(a,2) for x,y in it.combinations(b,2))
def blocks(f):
    return [tuple(i for i,x in enumerate(f) if x==a) for a in sorted(set(f))]
def majority(a,b,c):return b if b==c else a

def evaluate(G):
    H=tuple(i for i in range(11) if i not in G)
    target=canonical((G,H),11)
    cs={}
    for s,t in it.product(range(5),range(8)):
        q=[0]*11
        for u,i in enumerate(G):q[i]=cats['5'][s][u]
        for u,i in enumerate(H):q[i]=5+cats['6'][t][u]
        bs=blocks(q)
        if not any(crossing(a,b) for a,b in it.combinations(bs,2)):
            cs[s,t]=canonical(bs,11)
    acc={}
    for c in cs.values():
        delta=collections.defaultdict(int);delta[c]+=1
        for old,v in acc.items():delta[join(old,c)]-=v
        for q,v in delta.items():
            acc[q]=acc.get(q,0)+v
            if not acc[q]:del acc[q]
    relation=set(cs)
    closed=all((majority(a[0],b[0],c[0]),majority(a[1],b[1],c[1])) in relation for a,b,c in it.product(relation,repeat=3))
    covered=any(all(x==s or y==t for x,y in relation) for s,t in it.product(range(5),range(8)))
    return dict(pattern=target,connected=crossing(G,H),generators=len(cs),coefficient=acc.get(target,0),majority_closed=closed,covered=covered,relation=sorted(relation),original_generators=sorted(cs.values()))

rows=[evaluate(G) for G in it.combinations(range(11),5)]
catalogue=nc_certificates(4,1)+nc_certificates(1,3)
assert len(catalogue)==495
for row in rows:
    p=row['pattern']
    direct={canonical(bs,11) for bs in catalogue if all(len({p[i] for i in b})==1 for b in bs)}
    assert direct==set(row.pop('original_generators'))
old=json.loads((ROOT/'research/cross_domain_20261029/results56.json').read_text())
old_by_pattern={tuple(r['p']):r['coefficient'] for r in old['rows']}
connected=[r for r in rows if r['connected']]
assert all(old_by_pattern[r['pattern']]==r['coefficient'] for r in connected)
assert len(rows)==462 and len(connected)==451
assert collections.Counter(r['coefficient'] for r in connected)=={0:429,-1:22}
witness=next(r for r in rows if r['pattern']==(0,0,1,0,0,1,1,0,1,1,1))
assert witness['relation']==[(1,0),(2,4),(2,6)] and witness['coefficient']==-1
assert witness['covered'] and not witness['majority_closed']
out=dict(status='VERIFIED-COMP',patterns=462,connected=451,global_nc_catalogue_size=495,independent_generator_comparisons=462,prior_raw_maximal_run_mobius_agreements=451,
    connected_histogram=dict(collections.Counter(str(r['coefficient']) for r in connected)),
    relation_properties=dict(collections.Counter(str((r['majority_closed'],r['covered'],r['generators'],r['coefficient'])) for r in connected)),
    witness=witness,rows=rows)
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
