import core,json,pathlib,itertools,collections
D=pathlib.Path(__file__).resolve().parent
raw=json.loads((D/'classification.json').read_text());out=[]
def maximal(fs):
 fs=set(map(frozenset,fs));return {f for f in fs if not any(f<g for g in fs)}
def collapse(aa):
 fs=maximal(frozenset((i,v) for i,v in enumerate(a)) for a in aa);steps=[]
 while True:
  vs=set().union(*fs)
  if len(vs)<=1:return True,steps
  hit=None
  for v in sorted(vs):
   common=set.intersection(*(set(f) for f in fs if v in f))-{v}
   if common:hit=(v,min(common));break
  if not hit:return False,steps
  v,w=hit;steps.append([v,w]);fs=maximal(f-{v} for f in fs)
def main():
 for n,rs in raw['full_join_examples'].items():
  for r in rs:
   ok,steps=collapse(r['choices']);out.append({'n':int(n),'pattern':r['pattern'],'atoms':r['atoms'],'strongly_collapsed_to_point':ok,'steps':steps})
 # Exhaustive pair geometry; five options per class, relations recorded as degrees.
 pairtypes=collections.Counter();bad=[]
 for tail in itertools.combinations(range(1,10),4):
  A=(0,)+tail;B=tuple(i for i in range(10) if i not in A)
  aa,opts=core.atoms([A,B]);E=set(aa)
  if not core.cross(A,B):kind='noncrossing'
  elif not E:kind='empty'
  elif len({a for a,b in E})==1 or len({b for a,b in E})==1:kind='frozen'
  elif len(E)==2:kind='two_matching'
  elif len(E)==9 and any(E=={(a,b) for a in range(5) for b in range(5) if a==s or b==t} for s in range(5) for t in range(5)):kind='bistar'
  else:kind='OTHER';bad.append({'groups':[A,B],'choices':aa})
  pairtypes[kind]+=1
 r={'status':'VERIFIED-COMP','full_join_cases':out,'collapsed':sum(x['strongly_collapsed_to_point'] for x in out),'pair_types':dict(pairtypes),'pair_counterexamples':bad}
 (D/'structure.json').write_text(json.dumps(r,indent=2)+'\n');print({'cases':len(out),'collapsed':r['collapsed'],'pair_types':dict(pairtypes),'bad':len(bad)})

 assert r["collapsed"] == 38
 assert not bad
 assert dict(pairtypes) == {"noncrossing":5,"empty":51,"frozen":55,"bistar":10,"two_matching":5}

if __name__ == "__main__":
 main()
