"""Compress entire successful elementary traces into maximal Boolean intervals.

Every interval is independently checked against ALL cofaces in the live complex.
This explores arbitrary lower-face sizes, unlike the earlier <=3 search.
The trajectory is inherited from the earlier successful elementary trace;
compression is not a new existence proof or a universal collapse algorithm.
"""
from pathlib import Path
import hashlib,json,sys,tarfile,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import faces,bit_indices
SRC=ROOT/'research/fiber_elimination_20261030'
manifest=json.loads((SRC/'evidence_manifest.json').read_text());archive=SRC/'evidence.tar.gz'
assert hashlib.sha256(archive.read_bytes()).hexdigest()==manifest['archive_sha256']
rel='research/fiber_elimination_20261030/pr39-local-results.json'
with tarfile.open(archive) as t:data=t.extractfile(rel).read()
assert hashlib.sha256(data).hexdigest()==manifest['files'][rel]['sha256']
rows=[];start=time.monotonic()
for row in json.loads(data)['rows']:
    old=row['elementary_trace']
    if not old:continue
    vertex_map=row['elementary_vertex_map']
    rank={v:i for i,v in enumerate(vertex_map)}
    fs=[sum(1<<rank[v] for v in bit_indices(f)) for f in row['strong_core_facets']]
    F=faces(fs,300000);assert F is not None
    incidence={v:set() for f in F for v in bit_indices(f)}
    for f in F:
        for v in bit_indices(f):incidence[v].add(f)
    i=0;trace=[];hist={};initial=len(F)
    while i<len(old):
        lo=None;hi=0;collected=set();best=None
        for j in range(i,min(len(old),i+4096)):
            s,t=old[j]
            assert s!=t and s in F and t in F
            collected.update((s,t));lo=s&t if lo is None else lo&s&t;hi|=s|t
            if not lo:break
            count=len(collected)
            if count&(count-1)==0 and count==1<<(hi^lo).bit_count():
                # Equality of size and containment proves the complete Boolean interval.
                best=(j+1,lo,hi,set(collected))
        assert best is not None
        end,s,t,interval=best
        assert set.intersection(*(incidence[v] for v in bit_indices(s)))==interval
        assert s!=t and all(s&f==s and f&t==f for f in interval)
        assert sum((-1)**f.bit_count() for f in interval)==0
        for f in interval:
            F.remove(f)
            for v in bit_indices(f):incidence[v].remove(f)
        trace.append([s,t]);hist[s.bit_count()]=hist.get(s.bit_count(),0)+1;i=end
    assert len(F)==2 and 0 in F and max(F).bit_count()==1
    rows.append(dict(p=row['pattern'],vertex_map=vertex_map,initial_faces=initial,elementary_pairs=len(old),compressed_intervals=len(trace),lower_face_histogram=hist,largest_interval=max(1<<(t^s).bit_count() for s,t in trace),trace=trace))
    print(len(rows),'pairs',len(old),'intervals',len(trace),'lower_hist',hist,flush=True)
assert len(rows)==17
out=dict(status='VERIFIED-COMP',cases=len(rows),collapsed=17,elementary_pairs=sum(r['elementary_pairs'] for r in rows),compressed_intervals=sum(r['compressed_intervals'] for r in rows),rows=rows,seconds=time.monotonic()-start,
    compression_gain=sum(r['elementary_pairs']-r['compressed_intervals'] for r in rows),
    conclusion='The complete traces replay, but this contiguous-prefix compression obtains no gain on these inputs. No bounded-width or counting theorem is inferred.')
(HERE/'10_interval_compression.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='rows'},flush=True)
