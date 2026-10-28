from functools import lru_cache
from itertools import product
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
for q, maxn in [(2,12),(3,10),(4,8)]:
    checks=0
    winners=0
    for n in range(maxn+1):
        for w in product(range(q),repeat=n):
            if not win(w): continue
            winners+=1
            for i in range(n+1):
                for a in range(q):
                    for k in (2,3,4,5):
                        checks+=1
                        t=w[:i]+(a,)*k+w[i:]
                        assert win(t), (q,n,w,i,a,k,t)
    print(q,maxn,winners,checks,flush=True)
