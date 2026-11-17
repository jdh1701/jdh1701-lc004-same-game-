from math import factorial
from collections import Counter
from fractions import Fraction as F
import sys
def ncparts(pts):
    if not pts: yield []; return
    a=pts[0]; rest=pts[1:]
    # choose the other members of a's block as a subset of rest; gaps between consecutive members recursively
    L=len(rest)
    def choose(start, block, acc_gaps):
        # block so far; next member index >= start
        yield block, acc_gaps+[rest[start:]] if False else None
    def rec(idx, block):
        # option: close block now -> remaining rest[idx:] is the final gap
        yield block, idx
    # simple recursive: enumerate subsets of rest as block members in increasing order
    def gen(i, block):
        yield list(block), i
        for j in range(i, L):
            block.append(j); yield from gen(j+1, block); block.pop()
    for members, _ in gen(0, []):
        # gaps: between consecutive members (inner) and after last member (outer tail)
        idxs=[-1]+members
        gaps=[rest[idxs[t]+1:idxs[t+1]] for t in range(len(idxs)-1)] + [rest[(members[-1]+1 if members else 0):]]
        def prod(gl):
            if not gl: yield []; return
            for p in ncparts(gl[0]):
                for q in prod(gl[1:]): yield p+q
        for p in prod(gaps):
            yield [[a]+[rest[m] for m in members]]+p
def cotype(P,N):
    par=list(range(N))
    def f(x):
        while par[x]!=x: x=par[x]
        return x
    blockof={}
    for bi,B in enumerate(P):
        for x in B: blockof[x]=bi
    for a in range(N):
        for b in range(a+1,N):
            seg=set(range(a+1,b+1))
            if not any((set(B)&seg) and (set(B)-seg) for B in P): par[f(b)]=f(a)
    # also return outer face size (face containing gap N-1)
    g=Counter(f(x) for x in range(N)); return sorted(g.values()), g[f(N-1)], g
tot=bad=0; rotbad=0
for N in range(1,int(sys.argv[1])+1):
    cnt=Counter(); outer=Counter(); avg=Counter()
    for P in ncparts(list(range(N))):
        mu,dout,g=cotype(P,N); lam=tuple(sorted(len(b) for b in P)); mu=tuple(mu)
        cnt[(lam,mu)]+=1
        outer[(lam,mu,dout)]+=1
        for d in g.values(): avg[(lam,mu,d)]+=F(d,N)
    for (lam,mu),c in cnt.items():
        den=1
        for v in list(Counter(lam).values())+list(Counter(mu).values()): den*=factorial(v)
        pred=F(N*factorial(len(lam)-1)*factorial(len(mu)-1),den); tot+=1
        if pred!=c: bad+=1
    for key in set(outer)|set(avg):
        if outer[key]!=avg[key]: rotbad+=1
    print(f"N={N}: NC={sum(cnt.values())} type/cotype pairs={len(cnt)}",flush=True)
print("G5 GJ pairs checked:",tot,"mismatches:",bad,"| G6 rotation (type,cotype,outer-size) mismatches:",rotbad)
