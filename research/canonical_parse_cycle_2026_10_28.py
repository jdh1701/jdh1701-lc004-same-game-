from functools import lru_cache
from itertools import product
from collections import Counter

@lru_cache(None)
def win(w):
    if not w: return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]: j+=1
        if j-i>=2 and win(w[:i]+w[j:]): return True
        i=j
    return False

@lru_cache(None)
def parse(w):
    if not w: return (1,())
    n=len(w); a=w[0]; total=0; canonical=None
    for j in range(1,n):
        if w[j]!=a: continue
        l,lc=parse(w[1:j]); r,rc=parse(w[j+1:])
        if l and r:
            total+=l*r
            candidate=(2,j,lc,rc)
            if canonical is None or candidate<canonical: canonical=candidate
        if not l: continue
        for k in range(j+1,n):
            if w[k]!=a: continue
            m,mc=parse(w[j+1:k]); r,rc=parse(w[k+1:])
            if m and r:
                total+=l*m*r
                candidate=(3,j,k,lc,mc,rc)
                if canonical is None or candidate<canonical: canonical=candidate
    return total,canonical

for n in range(2,12):
    s=Counter()
    for w in product(range(3),repeat=n):
        winning=win(w); count,certificate=parse(w)
        assert winning==(count>0)
        assert (certificate is None)==(count==0)
        if winning:
            s['winning']+=1
            s['unique']+=(count==1)
            s['ambiguous']+=(count>1)
            s['derivations']+=count
    print(n,dict(s),flush=True)

assert parse((0,0,0,0))[0]==2
