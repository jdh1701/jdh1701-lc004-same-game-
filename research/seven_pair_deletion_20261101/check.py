"""Exact checks of the uniform seven-class pair-deletion identities.
The formula is proved on paper; these are exhaustive small geometries and
specified mixed-profile tests, not a census extrapolation.
"""
from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
from functools import lru_cache
import sys,json,random
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode,euler,maximal,local
from core import catalogue,blocks,crossing,canonical,generators,join_value,two_patterns
from fast_coefficient import all_five_coefficient,universal_seven_coefficient
C7=catalogue(7)
def norm(p):
 names={};return tuple(names.setdefault(x,len(names)) for x in p)
@lru_cache(None)
def data(p):return encode(p)
def coeff(p):return euler(data(norm(p))['facets'])
def connected(p):
 gs=blocks(p);seen={0}
 while True:
  new=seen|{j for i in seen for j,g in enumerate(gs) if crossing(gs[i],g)}
  if new==seen:return len(seen)==len(gs)
  seen=new

def on(g,c):return tuple(tuple(g[i] for i in b) for b in blocks(c))
# The fourteen nonsingleton local cut cliques, derived from certificates.
cliques=[]
for mask in range(63):
 cut=tuple(1 if i==0 else (mask>>(i-1))&1 for i in range(7))
 ts=tuple(t for t,c in enumerate(C7) if all(c[i]!=c[j] or cut[i]==cut[j] for i in range(7) for j in range(i)))
 if len(ts)>1:
  bs=blocks(cut);cliques.append((bs,ts))
assert len(cliques)==14
pairs=[(next(b for b in bs if len(b)==2),bs,ts) for bs,ts in cliques if len(ts)==5]
cut34=[bs for bs,ts in cliques if len(ts)==2]
assert len(pairs)==len(cut34)==7
stats=Counter();profiles=Counter();examples={};seen=set()

def check(p,source):
 p=norm(p)
 if p in seen:return
 seen.add(p)
 if not connected(p):return
 gs=blocks(p);seven=next(i for i,g in enumerate(gs) if len(g)==7);H=gs[seven];others=[g for i,g in enumerate(gs) if i!=seven]
 d=data(p);outmask=sum(1<<i for i,(g,t) in enumerate(d['labels']) if g!=seven)
 P=maximal(f&outmask for f in d['facets']);bp=euler(P);kp=euler(d['facets'])
 p0=tuple(x for x in p if x!=p[H[0]]);B=coeff(p0)
 universal=lambda bs:all(not crossing(a,b) for a in bs for b in others)
 u=sum(universal(on(H,c)) for c in C7)
 v=sum(universal(tuple(tuple(H[i] for i in b) for b in bs)) for bs in cut34)
 assert (u,v) in [(0,0),(1,0),(2,1),(5,0)]
 rank={v:i for i,v in enumerate(d['labels'])}
 outfacets=[]
 for a in d['choices']:
  f=0
  for i,s in enumerate(a):
   if i!=seven:
    for t in local(len(gs[i]))[s][1]:f|=1<<rank[i,t]
  outfacets.append(f)
 D=0;nonuniversal_D=0;terms=[]
 for pair,bs,ts in pairs:
  E=maximal(f|(1<<(len(d['labels'])+a[seven])) for a,f in zip(d['choices'],outfacets) if a[seven] in ts)
  ec=euler(E)
  actual=tuple(H[i] for i in pair)
  adjacent=any((a+1)%len(p)==b for a,b in [actual,actual[::-1]])
  uc=universal(tuple(tuple(H[i] for i in b) for b in bs))
  residual=tuple(x for x in H if x not in actual)
  residual_crossed=any(crossing(residual,g) for g in others)
  if adjacent:
   assert uc == (not residual_crossed)
   removed=tuple(x for i,x in enumerate(p) if i not in actual)
   dc=coeff(removed)
   assert ec==dc,(p,actual,ec,dc)
   D+=dc
   if not uc:nonuniversal_D+=dc
   if min(actual)==0 and max(actual)==len(p)-1:stats['wraparound_pair_checks']+=1
   terms.append({'pair':actual,'deletion_coefficient':dc,'universal_cut':uc})
  else:
   assert ec==0,(p,actual,ec)
   stats['nonadjacent_corrections_zero']+=1
  stats['pair_correction_checks']+=1
 assert kp==bp+(v-u)*B-D,(p,kp,bp,u,v,B,D)
 assert kp==(0 if u else bp)-nonuniversal_D
 if u:
  assert bp==B
  assert kp==-nonuniversal_D,(p,kp,nonuniversal_D)
  stats['universal_branch']+=1
 else:
  assert kp==bp-D
  stats['nonuniversal_branch']+=1
 if all(len(g)==5 for g in others):
  assert all_five_coefficient(p0)==B
  for term in terms:
   removed=tuple(x for i,x in enumerate(p) if i not in term['pair'])
   assert all_five_coefficient(removed)==term['deletion_coefficient']
   stats['fast_all_five_checks']+=1
  fast=universal_seven_coefficient(p)
  assert fast==(kp if u else None)
  if u:stats['fast_universal_seven_checks']+=1
 if kp:
  stats['nonzero']+=1
  key=f"u={u},v={v},sign={'positive' if kp>0 else 'negative'},outside_classes={len(others)}"
  examples.setdefault(key,{'pattern':p,'source':source,'coefficient':kp,'projected_beta':bp,'outside_coefficient':B,'u':u,'v':v,'pair_terms':terms})
 # Independent ORIGINAL signed-join replay on complete small families.
 if d['generators']<=12:
  cs,_,ch=generators(p)
  assert len(cs)==d['generators']
  assert join_value(cs,canonical(blocks(p),len(p)))==kp
  stats['direct_original_replays']+=1
 profiles[','.join(map(str,sorted(map(len,gs))))]+=1
 stats['connected_cases']+=1
 if stats['connected_cases']%500==0:print('checked',stats['connected_cases'],flush=True)

for other in [5,6,7]:
 for p in two_patterns(other,7):check(p,f'exhaustive-{other}-7')
# A documented nonzero witness whose projection has beta +1.
w=(0,2,2,0,1,1,2,2,1,2,2,1,1,0,0,2,0)
check(w,'PR50-nonzero-majority-obstruction')
# Guard target-label normalization: the signed-join dictionary uses canonical
# partitions. Replay every relabeling of a NONZERO witness, not only a zero.
for perm in permutations(range(3)):
 p=tuple(perm[x] for x in w);cs,_,_=generators(p)
 assert join_value(cs,canonical(blocks(p),len(p)))==1
 stats['nonzero_relabeling_guards']+=1
# The old zero witness remains zero after correcting its target normalization.
p=(1,1,0,0,0,2,2,0,0,2,1,1,2,2,1,2,2)
cs,_,_=generators(p);assert join_value(cs,canonical(blocks(p),len(p)))==0
# Fixed, previously verified all-five source cores. Inflate every doubled edge
# by two points, giving positive higher-excess cases rather than mostly empty
# random inputs. This is a source family, not an exhaustive target census.
for j in [3,4,5]:
 for line in (ROOT/f'research/primitive_core_20261031/sample_{j}.txt').read_text().splitlines():
  vals=list(map(int,line.split()));word=[None]*(3*j);weights=[0]*(3*j)
  for i in range(j):
   x0,x1,x2,r,u,d=vals[6*i:6*i+6]
   for x in [x0,x1,x2]:word[x]=i;weights[x]=1 if x==r else 2
  source=tuple(c for c,k in zip(word,weights) for _ in range(k))
  assert coeff(source)==-1
  # Tripling a singleton root is a different operation from lengthening a
  # pair-run. It has a uniform coefficient multiplier -2.
  roots=[i for i in range(len(source)) if source[i]!=source[(i-1)%len(source)] and source[i]!=source[(i+1)%len(source)]]
  assert len(roots)==j
  for i in roots:
   target=source[:i]+(source[i],)*2+source[i:]
   assert coeff(target)==2
   assert universal_seven_coefficient(target)==2
   stats['singleton_tripling_checks']+=1
   check(target,f'root-tripling-j{j}')
  # Repeated tripling: every subset for j=3, and subsets of size at most
  # two for j=4. Compute the COMPLETE original separator complex afresh.
  # The larger j=5 fixtures above test one tripling only.
  if j<=4:
   for size in range(2,(j if j==3 else 2)+1):
    for chosen in combinations(roots,size):
     target=tuple(x for i,x in enumerate(source) for _ in range(3 if i in chosen else 1))
     assert coeff(target)==(-1)**(size+1)*2**size
     stats[f'iterated_tripling_s{size}_checks']+=1
     check(target,f'iterated-root-tripling-j{j}-s{size}')
  for i in range(len(source)):
   if source[i]==source[(i+1)%len(source)]:
    check(source[:i]+(source[i],)*2+source[i:],f'verified-star-inflation-j{j}')
# Fixed-seed mixed-profile checks for the arbitrary-outside-size identity.
rng=random.Random(20261102)
for profile in [(5,5,7),(5,6,7),(6,6,7),(5,5,5,7)]:
 pool=sum(([i]*n for i,n in enumerate(profile)),[])
 for _ in range(100):
  rng.shuffle(pool);check(tuple(pool),'seeded-mixed-profile')
# Orbit-aware small family count: all five connected (5,5) survivors,
# every subset of their classes, and ALL cyclic rootings of the targets.
sources=[p for p in two_patterns(5,5) if connected(p) and coeff(p)]
assert len(sources)==5
family_counts={}
for size in range(3):
 targets=set()
 for source in sources:
  roots=[i for i in range(len(source)) if source[i]!=source[(i-1)%len(source)] and source[i]!=source[(i+1)%len(source)]]
  assert len(roots)==2
  for chosen in combinations(roots,size):
   target=tuple(x for i,x in enumerate(source) for _ in range(3 if i in chosen else 1))
   for cut in range(len(target)):targets.add(norm(target[cut:]+target[:cut]))
 assert len(targets)==[5,12,7][size]
 for target in targets:
  assert coeff(target)==(-1)**(size+1)*2**size
  cs,_,_=generators(target)
  assert join_value(cs,canonical(blocks(target),len(target)))==coeff(target)
  stats['tripling_family_original_replays']+=1
 family_counts[size]=len(targets)
result={'status':'VERIFIED-COMP','statistics':dict(sorted(stats.items())),
 'profiles':dict(sorted(profiles.items())),'examples':dict(sorted(examples.items())),
 'random_seed':20261102,'random_trials_per_profile':100,'random_profiles':[(5,5,7),(5,6,7),(6,6,7),(5,5,5,7)],
 'tripling_family_counts_j2':family_counts,
 'proof_scope':'The identities are uniform paper proofs; tests do not establish a census or the full LC004 enumeration.'}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='examples'},indent=2))
