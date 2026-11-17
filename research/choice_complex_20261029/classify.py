import core,json,pathlib,collections,time,gzip
D=pathlib.Path(__file__).resolve().parents[1]
source=D/'all_five_adversarial_20261029/results.json'
text=source.read_text() if source.exists() else gzip.decompress(source.with_suffix('.json.gz').read_bytes()).decode()
rows=json.loads(text)['three_plus_cases'];counts=collections.Counter();examples={};start=time.time()
for r in rows:
 p=r['pattern'];groups=[tuple(i for i,x in enumerate(p) if x==c) for c in sorted(set(p))];aa,_=core.atoms(groups)
 frozen=[i for i in range(len(groups)) if len({a[i] for a in aa})==1]
 k='frozen_coordinate' if frozen else 'full_join'
 counts[(r['n'],k)]+=1
 if k=='full_join':examples.setdefault(r['n'],[]).append({**r,'choices':aa})
out={'status':'VERIFIED-COMP','counts':[{'n':n,'type':k,'count':v} for (n,k),v in counts.items()],'full_join_examples':examples,'seconds':time.time()-start}
(D/'choice_complex_20261029/classification.json').write_text(json.dumps(out,indent=2)+'\n');print(out['counts'])
