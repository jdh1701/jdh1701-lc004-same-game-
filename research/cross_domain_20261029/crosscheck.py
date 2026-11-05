"""Independent signed certificate-join calculation; no raw-game calls."""
import json,itertools,pathlib,collections
from functools import lru_cache
D=pathlib.Path(__file__).resolve().parent
@lru_cache(None)
def cert_parts(S):
 if not S:return ((),)
 out=[];a=S[0]
 for k in (2,3):
  for tail in itertools.combinations(S[1:],k-1):
   B=(a,)+tail
   for rest in cert_parts(tuple(x for x in S if x not in B)):out.append((B,)+rest)
 return tuple(out)
def canon(w):
 d={};return tuple(d.setdefault(a,len(d)) for a in w)
def join(p,q):
 a=list(p)
 for i in range(len(q)):
  for j in range(i):
   if q[i]==q[j] and a[i]!=a[j]:
    x,y=a[i],a[j];a=[y if z==x else z for z in a]
 return canon(a)
count=0
for fn in ('results.json','results56.json','results57sample.json'):
 data=json.loads((D/fn).read_text())
 for row in data['rows']:
  p=tuple(row['p']);n=len(p);B=[tuple(i for i,x in enumerate(p) if x==c) for c in sorted(set(p))];cert=[]
  for x,y in itertools.product(*(cert_parts(b) for b in B)):
   q=[0]*n
   for k,b in enumerate(x+y):
    for i in b:q[i]=k
   if any(q[a]==q[c] and q[b]==q[d] and q[a]!=q[b] for a,b,c,d in itertools.combinations(range(n),4)):continue
   cert.append(canon(q))
  assert len(cert)==row['certificates']
  acc={tuple(range(n)):1}
  for q in cert:
   nxt=collections.defaultdict(int,acc)
   for r,v in acc.items():nxt[join(r,q)]-=v
   acc={r:v for r,v in nxt.items() if v}
  assert -acc.get(p,0)==row['coefficient'],row
  count+=1
out={'status':'VERIFIED-COMP','independent_signed_join_checks':count}
(D/'crosscheck.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
