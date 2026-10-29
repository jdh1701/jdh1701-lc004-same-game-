"""Raw-game Mobius checks of counterexamples and higher-order generators."""
import pathlib,runpy,json,itertools,math
D=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(D/'noncrossing_components_20261029/check_components.py'))
patterns,canon,win=(d[k] for k in ['patterns','canon','win'])
a=json.loads((D/'overlap_20261029/higher67.json').read_text());witnesses={tuple(w['pattern']):{'coefficient':w['actual']} for w in a['pair_graph_mismatches']}
checks=[]
for p,w in witnesses.items():
 B=[tuple(i for i,x in enumerate(p) if x==c) for c in sorted(set(p))];v=0
 for us in itertools.product(*(list(patterns(len(b))) for b in B)):
  q=[0]*len(p);mu=1;offset=0
  for b,u in zip(B,us):
   k=len(set(u));mu*=(-1)**(k-1)*math.factorial(k-1)
   for i,x in zip(b,u):q[i]=offset+x
   offset+=k
  v+=mu*win(canon(q))
 assert v==w['coefficient'];checks.append({'p':p,'coefficient':v})
out={'status':'VERIFIED-COMP','independent_raw_mobius_witnesses':checks}
(D/'overlap_20261029/verification67.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
