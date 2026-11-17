"""Attacks 6--9: graphs, topology, profile compression, cyclic core."""
from core import *
import json,collections,time,random
HERE=Path(__file__).resolve().parent
start=time.time();rows=[];collapses=[];graph_fail=None;signature_fail=None;core_fail=None
by_signature={};by_core={};hist=collections.Counter();max_circuit=0;minimal_circuit_example=None

def cyc_core(p):
    r=[p[i] for i in range(len(p)) if i==0 or p[i]!=p[i-1]]
    if len(r)>1 and r[0]==r[-1]:r.pop()
    return len(r) # two-color cyclic alternating core is determined by this length

def graph_prediction(cs,p):
    m=len(cs)
    if m>20:return None,None
    edges={ (i,j) for i,j in combinations(range(m),2) if join(cs[i],cs[j])==p }
    # - reduced Euler of the complex avoiding pairwise top joins.
    independent=[0]*(1<<m);independent[0]=1;value=1
    adj=[sum(1<<j for j in range(m) if (min(i,j),max(i,j)) in edges) for i in range(m)]
    for s in range(1,1<<m):
        b=s&-s;i=b.bit_length()-1;rest=s^b
        independent[s]=independent[rest] and not(rest&adj[i])
        if independent[s]:value+=(-1)**s.bit_count()
    # Coefficient = sum (-1)^|S| over proper-join subsets for m>0.
    return value,len(edges)

for a,b in [(5,6),(5,7),(6,6),(5,8)]:
    for p in two_patterns(a,b):
        gs=blocks(p)
        if not crossing(*gs):continue
        cs,fs,choices=generators(p);m=len(cs)
        fj=full_join(cs,len(p))==p
        F=faces(fs);val=sum((-1)**len(f) for f in F)
        if not fj:assert val==0
        # Independent original partition-join check for every full-support case;
        # also all (5,6), whose old census supplies a third oracle.
        if fj or (a,b)==(5,6):assert join_value(cs,p)==val,(p,m,val)
        reduced,steps=strong_collapse(fs)
        sphere=homology_f2(F) if fj else []
        reducedF=faces(reduced)
        assert sum((-1)**len(f) for f in reducedF)==val
        if val==0 and fj:collapses.append(dict(p=p,generators=m,facets=[sorted(f) for f in fs],steps=steps,remaining=[sorted(f) for f in reduced],homology=sphere))
        profile=tuple(sorted(map(len,gs)))
        sig=(profile,m)
        if sig in by_signature and by_signature[sig][1]!=val and signature_fail is None:
            signature_fail=dict(signature=sig,left=by_signature[sig],right=(p,val))
        by_signature.setdefault(sig,(p,val))
        sigc=(profile,cyc_core(p))
        if sigc in by_core and by_core[sigc][1]!=val and core_fail is None:
            core_fail=dict(signature=sigc,left=by_core[sigc],right=(p,val))
        by_core.setdefault(sigc,(p,val))
        gp=None
        if fj and m<=16:
            gp,edges=graph_prediction(cs,p)
            if gp!=val and graph_fail is None:graph_fail=dict(p=p,generators=cs,actual=val,pairwise_graph_prediction=gp,edges=edges)
            # Minimal three-generator top join missed by every pair.
            if minimal_circuit_example is None:
                for inds in combinations(range(m),3):
                    sub=[cs[i] for i in inds]
                    if full_join(sub,len(p))==p and all(join(c,d)!=p for c,d in combinations(sub,2)):
                        minimal_circuit_example=dict(p=p,generators=sub);break
        row=dict(p=p,profile=profile,generators=m,coefficient=val,full_join=fj,facets=len(maximal(fs)),vertices=len(set().union(*fs)) if fs else 0,faces=len(F),remaining_vertices=len(set().union(*reduced)) if reduced else 0,homology=sphere,graph_value=gp)
        rows.append(row);hist[str((profile,m,val,fj,row['remaining_vertices']))]+=1
    print('finished',a,b,'rows',len(rows),'seconds',round(time.time()-start,2),flush=True)

old=json.loads((ROOT/'research/mixed_kernel_20261030/results.json').read_text())['rows']
old={tuple(r['pattern']):r['coefficient'] for r in old if r['connected']}
assert all(old[tuple(r['p'])]==r['coefficient'] for r in rows if r['profile']==(5,6))
out=dict(status='VERIFIED-COMP',rows=rows,histogram=dict(hist),same_profile_count_counterexample=signature_fail,cyclic_core_counterexample=core_fail,pairwise_graph_counterexample=graph_fail,minimal_three_way_join=minimal_circuit_example,
         zero_full_join_cases=len(collapses),zero_full_join_strongly_collapsed=sum(len(set().union(*(set(map(tuple,f)) for f in r['remaining'])))==1 for r in collapses),seconds=time.time()-start)
(HERE/'topology.json').write_text(json.dumps(out,indent=2)+'\n')
(HERE/'collapse_certificates.json').write_text(json.dumps(collapses,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('rows','histogram')},indent=2),flush=True)
