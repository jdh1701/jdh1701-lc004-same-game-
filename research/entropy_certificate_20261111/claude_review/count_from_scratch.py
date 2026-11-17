"""Claude review, 2026-11-12. From-scratch W_3(n): (a) brute force on the original maximal-run game,
(b) fusion-stack support DP with colour-orbit merging. Independent of all repository code.
Usage: python count_from_scratch.py BRUTE_MAX FUSION_MAX"""
import itertools, sys
from functools import lru_cache
from collections import Counter
@lru_cache(None)
def wins(w):
    if not w: return True
    i=0
    while i<len(w):
        j=i
        while j<len(w) and w[j]==w[i]: j+=1
        if j-i>=2 and wins(w[:i]+w[j:]): return True
        i=j
    return False
def step(S,a):
    o=set()
    for s in S:
        if s and s[-1]==a: o.add(s); o.add(s[:-1])
        else: o.add(s+(a,))
    return frozenset(o)
def canon(S):
    return min(tuple(sorted(tuple(p[c] for c in s) for s in S)) for p in itertools.permutations((0,1,2)))
bm,fm=map(int,sys.argv[1:3])
for n in range(1,bm+1): print('brute',n,sum(wins(w) for w in itertools.product((0,1,2),repeat=n)),flush=True)
cur=Counter({frozenset([()]):1})
for n in range(1,fm+1):
    m={}
    for S,c in cur.items():
        for a in (0,1,2):
            T=step(S,a); k=canon(T)
            m[k]=(m[k][0],m[k][1]+c) if k in m else (T,c)
    cur=Counter({S:c for S,c in m.values()})
    print('fusion',n,sum(c for S,c in cur.items() if () in S),'orbits',len(cur),flush=True)
