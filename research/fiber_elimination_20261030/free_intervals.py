"""Test free intervals with lower faces of at most three vertices.

Source cores come from the locally rerun, exact-source-green PR39 rescue.
Search uses facet incidence; replay checks ALL cofaces in the explicit complex.
Failure to find a small free interval is recorded as a stall, never a disproof.
"""
from pathlib import Path
from itertools import combinations
import argparse,hashlib,json,tarfile,time
from fast_complex import maximal,faces,bit_indices

HERE=Path(__file__).resolve().parent
name='pr39-local-results.json'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--archive-input',action='store_true')
args=parser.parse_args()
if (HERE/name).exists() and not args.archive_input:
    data=(HERE/name).read_bytes()
else:
    manifest=json.loads((HERE/'evidence_manifest.json').read_text())
    archive=HERE/'evidence.tar.gz'
    assert hashlib.sha256(archive.read_bytes()).hexdigest()==manifest['archive_sha256']
    rel='research/fiber_elimination_20261030/'+name
    with tarfile.open(archive,'r:gz') as tar:data=tar.extractfile(rel).read()
    assert hashlib.sha256(data).hexdigest()==manifest['files'][rel]['sha256']
inputs=json.loads(data)['rows']

def search(fs):
    fs=maximal(fs);trace=[]
    for step in range(100000):
        if len(fs)==1 and fs[0].bit_count()==1:return fs,trace,True
        incidence={}
        for j,f in enumerate(fs):
            for v in bit_indices(f):incidence[v]=incidence.get(v,0)|(1<<j)
        chosen=None
        for k in range(1,4):
            for vs in combinations(sorted(incidence),k):
                hits=incidence[vs[0]]
                for v in vs[1:]:hits&=incidence[v]
                if hits and hits&(hits-1)==0:
                    t=fs[hits.bit_length()-1];s=sum(1<<v for v in vs)
                    if s!=t:chosen=s,t;break
            if chosen:break
        if chosen is None:return fs,trace,False
        s,t=chosen
        assert [f for f in fs if s&f==s]==[t] and s&t==s
        # The surviving part of tau is the union of tau minus each lower vertex.
        fs=maximal([f for f in fs if f!=t]+[t^(1<<v) for v in bit_indices(s)])
        trace.append([s,t])
    raise RuntimeError('explicit 100000-interval budget')

def replay(initial,trace):
    F=faces(initial,cap=300000);assert F is not None
    incidence={}
    for f in F:
        for v in bit_indices(f):incidence.setdefault(v,set()).add(f)
    initial_faces=len(F);removed=0
    for s,t in trace:
        assert s and s!=t and s&t==s and s.bit_count()<=3
        cofaces=set.intersection(*(incidence[v] for v in bit_indices(s)))
        free=t^s;interval=set();u=free
        while True:
            interval.add(s|u)
            if not u:break
            u=(u-1)&free
        assert cofaces==interval
        assert sum((-1)**f.bit_count() for f in interval)==0
        for f in interval:
            F.remove(f)
            for v in bit_indices(f):incidence[v].remove(f)
        removed+=len(interval)
    return F,initial_faces,removed

start=time.monotonic();rows=[]
for r in inputs:
    if not r['elementary_trace']:continue
    initial=r['strong_core_facets'];final,trace,ok=search(initial)
    remaining,count,removed=replay(initial,trace)
    assert remaining==faces(final,cap=300000)
    if ok:assert len(remaining)==2 and 0 in remaining
    row=dict(p=r['pattern'],status='collapsed' if ok else 'stalled-inconclusive',
        initial_faces=count,remaining_faces=len(remaining),intervals=len(trace),
        removed_faces=removed,max_interval=max(1<<(t^s).bit_count() for s,t in trace),trace=trace)
    rows.append(row)
    print('case',len(rows),row['status'],'faces',count,'intervals',len(trace),'remaining',len(remaining),flush=True)
out=dict(status='VERIFIED-COMP',cases=len(rows),collapsed=sum(r['status']=='collapsed' for r in rows),rows=rows,seconds=time.monotonic()-start)
assert len(rows)==17
(HERE/'free_intervals.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',out['cases'],'collapsed',out['collapsed'],'seconds',out['seconds'],flush=True)
