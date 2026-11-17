"""Independent raw maximal-run counts versus the connected-weight expansion."""
import runpy,pathlib,itertools,json,math
root=pathlib.Path(__file__).resolve().parents[1]
d=runpy.run_path(str(root/'noncrossing_components_20261029/check_components.py'))
patterns,closure,blocks,canon,win,coeff=(d[k] for k in ['patterns','closure','blocks','canon','win','coeff'])
rows=[]
for b in range(4):
 k={}
 for n in range(8):
  ps=list(patterns(n))
  k[n]=sum(coeff[n][p]*b**len(set(p)) for p in ps if closure(p)==(0,)*n)
  expanded=sum(math.prod(k[len(block)] for block in blocks(p)) for p in ps if closure(p)==p)
  raw=sum(win(canon(w)) for w in itertools.product(range(b),repeat=n))
  assert expanded==raw,(b,n,expanded,raw)
  rows.append({'b':b,'n':n,'count':raw,'connected_weight':k[n]})
out={'status':'VERIFIED-COMP','scope':'b=0..3, n=0..7, exact integers and raw maximal-run solver','cases':len(rows),'rows':rows}
pathlib.Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
