# Usage: python3 claude_check_signed_mobius.py 10   (about 90 s; writes signed_10.json)
# Independent check (Claude): signed join coefficients via partition-lattice Mobius, h from legal whole-run play.
import sys, json
from functools import lru_cache
from itertools import groupby
from math import factorial
N=int(sys.argv[1])
@lru_cache(None)
def wins(w):
    if not w: return True
    i=0
    for _,g in groupby(w):
        L=len(list(g))
        if L>=2 and wins(w[:i]+w[i+L:]): return True
        i+=L
    return False
def rgs(n):
    def rec(pre,m):
        if len(pre)==n: yield tuple(pre); return
        for c in range(m+2):
            yield from rec(pre+[c],max(m,c))
    yield from rec([],-1)
def canon(w):
    d={};return tuple(d.setdefault(x,len(d)) for x in w)
def classes(p):
    k=max(p)+1 if p else 0
    C=[[] for _ in range(k)]
    for i,c in enumerate(p): C[c].append(i)
    return C
def setparts(lst):
    if not lst: yield []; return
    f,rest=lst[0],lst[1:]
    for sp in setparts(rest):
        yield [[f]]+sp
        for j in range(len(sp)):
            yield sp[:j]+[[f]+sp[j]]+sp[j+1:]
def cross(A,B):
    # alternating a<b<a<b or b<a<b<a
    s=sorted([(x,0) for x in A]+[(x,1) for x in B]); seq=[t for _,t in s]
    alt=[k for k,_ in groupby(seq)]
    return len(alt)>=4
def connected(C):
    blocks=[set(c) for c in C]
    changed=True
    while changed:
        changed=False
        for i in range(len(blocks)):
            for j in range(i+1,len(blocks)):
                if cross(blocks[i],blocks[j]):
                    blocks[i]|=blocks[j]; del blocks[j]; changed=True; break
            if changed: break
    return len(blocks)==1
results={}
for n in range(1,N+1):
    kappa={}
    viol=0; nz=0
    for p in rgs(n):
        C=classes(p)
        # c(p)=sum_{r<=p} mu(r,p) h(r); mu = prod over classes (-1)^(k-1)(k-1)!
        acc=[0]
        def rec(i,word,mu):
            if i==len(C):
                if wins(canon(tuple(word))): acc[0]+=mu
                return
            for sp in setparts(C[i]):
                k=len(sp); w=list(word)
                base=max(w)+1 if any(x>=0 for x in w) else 0
                for t,blk in enumerate(sp):
                    for pos in blk: w[pos]=base+t
                rec(i+1,w,mu*((-1)**(k-1))*factorial(k-1))
        rec(0,[-1]*n,1)
        tot=acc[0]
        if tot!=0 and connected(C):
            nz+=1
            kappa[len(C)]=kappa.get(len(C),0)+tot
            if len(C)>=2 and min(len(c) for c in C)<5: viol+=1
    results[n]={"kappa":{str(k):v for k,v in sorted(kappa.items())},"violations":viol,"nonzero_connected":nz}
    print(n,results[n],flush=True)
json.dump(results,open(f"signed_{N}.json","w"),indent=1)
