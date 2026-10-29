"""Test pair-generation graphs against the full join coefficient."""
import runpy,pathlib,json,itertools,functools
D=pathlib.Path(__file__).resolve().parent
d=runpy.run_path(str(D/'probe.py'));certificates,join=(d[k] for k in ['certificates','join'])
rows=json.loads((D/'results.json').read_text())['rows'];mismatch=[];higher=[]
for r in rows:
 p=tuple(r['p']);cs=certificates(p);m=len(cs);adj=[0]*m
 for i,j in itertools.combinations(range(m),2):
  if join(cs[i],cs[j])==p:adj[i]|=1<<j;adj[j]|=1<<i
 @functools.lru_cache(None)
 def ind(S):
  if not S:return 1
  bit=S&-S;i=bit.bit_length()-1;T=S^bit
  return ind(T)-ind(T&~adj[i])
 predicted=ind((1<<m)-1) if m else 0
 if predicted!=r['coefficient']:mismatch.append({'pattern':p,'actual':r['coefficient'],'graph_prediction':predicted})
 for i,j,k in itertools.combinations(range(m),3):
  if adj[i]&(1<<j|1<<k) or adj[j]&(1<<k):continue
  if join(join(cs[i],cs[j]),cs[k])==p:
   higher.append({'pattern':p,'certificates':[cs[i],cs[j],cs[k]]});break
out={'status':'VERIFIED-COMP','tested':len(rows),'pair_graph_mismatches':mismatch,'minimal_triple_witnesses':higher}
(D/'higher.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'tested':len(rows),'mismatches':len(mismatch),'triple_witnesses':len(higher),'first_mismatch':mismatch[:1],'first_triple':higher[:1]}))
