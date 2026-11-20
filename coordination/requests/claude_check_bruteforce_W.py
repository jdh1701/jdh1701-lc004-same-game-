# Claude independent check for R-2026-11-20: brute-force W_n(q) by legal whole-run play vs transfer.json.
# Usage: python3 claude_check_bruteforce_W.py <unpacked bundle>/expected/transfer.json 13
import json,sys
from functools import lru_cache
from itertools import groupby
@lru_cache(None)
def wins(w):
    if not w: return True
    i=0
    for _,g in groupby(w):
        L=len(list(g))
        if L>=2:
            r=w[:i]+w[i+L:]
            d={};r=tuple(d.setdefault(x,len(d)) for x in r)
            if wins(r): return True
        i+=L
    return False
def rgs(n):
    def rec(pre,m,cnt):
        if len(pre)==n:
            if all(c>=2 for c in cnt): yield tuple(pre)
            return
        rem=n-len(pre)
        need=sum(1 for c in cnt if c<2)
        if need>rem: return
        for c in range(m+2):
            if c<=m: cnt[c]+=1; yield from rec(pre+[c],m,cnt); cnt[c]-=1
            else: cnt.append(1); yield from rec(pre+[c],c,cnt); cnt.pop()
    yield from rec([],-1,[])
t=json.load(open(sys.argv[1]))
ff=lambda q,j: __import__('math').prod(q-i for i in range(j))
for n in range(1,int(sys.argv[2])+1):
    A={}
    for p in rgs(n):
        if wins(p): A[max(p)+1]=A.get(max(p)+1,0)+1
    W=t['W'][str(n)]
    bad=[q for q in range(0,7) if sum(a*ff(q,j) for j,a in A.items())!=sum(c*q**i for i,c in enumerate(W))]
    print(n,"mismatch q:",bad,flush=True)
