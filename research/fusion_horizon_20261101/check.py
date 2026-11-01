from pathlib import Path
import sys,json,subprocess,itertools,collections
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research/global_fusion_20261101'))
from fusion import support,step,proper,weighted
ps=tuple(itertools.permutations(range(3)))
def canon(S):
    S=tuple(S)
    return min(tuple(sorted(tuple(p[a] for a in (s[::-1] if rev else s)) for s in S)) for rev in [False,True] for p in ps)
def direct_count(n):
    states={((),):1}
    for k in range(n):
        nxt=collections.defaultdict(int)
        for S,c in states.items():
            for a in range(3):
                T=canon(s for s in step(S,a) if len(s)<=n-k-1)
                if T:nxt[T]+=c
        states=nxt
    return sum(c for S,c in states.items() if () in S)
known=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349]
rows=[]
for n,x in enumerate(known):
    p=subprocess.run([sys.argv[1],str(n),'2000000'],capture_output=True,text=True,check=True)
    r=json.loads(p.stdout);assert r['count']==x
    if n<=14:assert direct_count(n)==x
    rows.append(r)
# Arbitrary finite sets, including sets that need not be reachable from a word.
pool=[w for n in range(3) for w in itertools.product(range(3),repeat=n) if proper(w)]
index={w:i for i,w in enumerate(pool)};counts=[[0]*6 for _ in range(1<<len(pool))]
for n in range(6):
    for w in itertools.product(range(3),repeat=n):
        mask=0
        for i,s in enumerate(pool):
            S={s}
            for a in w:S=step(S,a)
            if () in S:mask|=1<<i
        for S in range(len(counts)):counts[S][n]+=bool(S&mask)
for S in range(len(counts)):
    R=sum(1<<index[s[::-1]] for i,s in enumerate(pool) if S>>i&1)
    assert counts[S]==counts[R]
anti=0;nonlump=None
for n in range(9):
    for w in itertools.product(range(3),repeat=n):
        S=support(w);R=frozenset(s[::-1] for s in S)
        assert support(w[::-1])==R;anti+=1
        if nonlump is None:
            x=collections.Counter(canon(step(S,a)) for a in range(3));y=collections.Counter(canon(step(R,a)) for a in range(3))
            if x!=y:nonlump={'word':w,'support':sorted(S),'reversed_support':sorted(R),'successors':sorted(x.items()),'reversed_successors':sorted(y.items())}
# Exact proper-basis trace pairing: no unproved multiplicity normalization.
pairings=0
for s in pool:
    for t in pool:
        assert weighted(s+t).get((),0)==int(s==t[::-1]);pairings+=1
result={'status':'VERIFIED-COMP','cpp_counts':rows,'independent_python_counts_through':14,'arbitrary_support_sets':len(counts),'arbitrary_suffix_max_length':5,'word_reversal_support_checks':anti,'proper_basis_trace_checks':pairings,'not_strongly_lumpable_witness':nonlump,'scope':'Exact finite checks. The reversal averaging theorem is proved on paper; Lean formalizes horizon soundness and individual-continuation minimality.'}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cpp_counts'},indent=2))
