"""Enumerate the exact missing-face correction on two graph counterexamples."""
import runpy,pathlib,json,itertools,collections
D=pathlib.Path(__file__).resolve().parent
d=runpy.run_path(str(D/'probe.py'));certificates,join=(d[k] for k in ['certificates','join'])
rows=[]
for w in json.loads((D/'higher67.json').read_text())['pair_graph_mismatches']:
 p=tuple(w['pattern']);cs=certificates(p);edges=[(i,j) for i,j in itertools.combinations(range(len(cs)),2) if join(cs[i],cs[j])==p];hist=collections.Counter()
 for mask in range(1<<len(cs)):
  if any(mask>>i&1 and mask>>j&1 for i,j in edges):continue
  q=tuple(range(len(p)))
  for i,c in enumerate(cs):
   if mask>>i&1:q=join(q,c)
  if q==p:hist[mask.bit_count()]+=1
 correction=sum((-1)**k*v for k,v in hist.items())
 assert correction==w['graph_prediction']-w['actual']
 rows.append({**w,'missing_generating_faces_by_size':dict(hist),'alternating_correction':correction})
(D/'correction.json').write_text(json.dumps({'status':'VERIFIED-COMP','rows':rows},indent=2)+'\n');print(rows)
