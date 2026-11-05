"""Independent exhaustive check of the finite table in PROOF.md."""
import itertools,json,pathlib
import core
table=[
 ('0000011111',5,{(a,b) for a in range(5) for b in range(5)}),
 ('0000101111',10,set()),
 ('0000110111',20,{(a,0) for a in range(5)}),
 ('0001010111',10,set()),
 ('0001011011',20,{(4,2)}),
 ('0001011101',5,{(4,1)}),
 ('0001100111',10,{(a,0) for a in range(5)}|{(4,b) for b in range(5)}),
 ('0001101011',10,set()),
 ('0010011011',5,{(0,2),(3,4)}),
 ('0010101011',10,set()),
 ('0010101101',10,set()),
 ('0010110011',10,{(0,2)}),
 ('0101010101',1,set())]
seen=set();rows=[]
def m(x,y,z):return y if y==z else x
for s,count,E in table:
 w=tuple(map(int,s));orbit=set()
 for z in (w,w[::-1]):
  for r in range(10):
   v=z[r:]+z[:r]
   orbit.add(v if v[0]==0 else tuple(1-x for x in v))
 assert len(orbit)==count and not orbit&seen
 seen|=orbit
 groups=[tuple(i for i,x in enumerate(w) if x==a) for a in range(2)]
 choices,opts=core.atoms(groups);assert set(choices)==E
 for group,options in zip(groups,opts):
  expected=[tuple(group[i] for i in pair) for pair in [(0,1),(0,4),(1,2),(2,3),(3,4)]]
  assert [P for P,T in options]==expected
 for a,b,c in itertools.product(E,repeat=3):
  assert (m(a[0],b[0],c[0]),m(a[1],b[1],c[1])) in E
 rows.append({'representative':s,'size':count,'compatible_pairs':sorted(E)})
assert len(seen)==126
assert seen=={(0,)+w for w in itertools.product(range(2),repeat=9) if sum(w)==5}
out={'status':'VERIFIED-COMP','orbits':13,'patterns':126,'majority_closure':'all relations pass','rows':rows}
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('VERIFIED-COMP: 13 disjoint orbits cover all 126 patterns; table and majority closure agree')
