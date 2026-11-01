"""Boolean fusion support, with an exact original-game semantics proof.

Python tuples store the TOP LAST; the Lean file stores the TOP FIRST.
This implementation is independently written from the encoded C++ version.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import permutations

def step(states, a):
    out=set()
    for s in states:
        if s and s[-1]==a:
            out.add(s)
            out.add(s[:-1])
        else:
            out.add(s+(a,))
    return frozenset(out)

@lru_cache(None)
def support(w):
    if not w:return frozenset({()})
    return step(support(w[:-1]),w[-1])

def weighted(w, stay_weight=1):
    """Counts fusion paths, NOT distinct winning words."""
    cur={():1}
    for a in w:
        nxt=defaultdict(int)
        for s,c in cur.items():
            if s and s[-1]==a:
                nxt[s]+=stay_weight*c
                nxt[s[:-1]]+=c
            else:nxt[s+(a,)]+=c
        cur=nxt
    return dict(cur)

def count(q, n, cap=300000):
    ps=tuple(permutations(range(q)))
    def canon(S):
        return min(tuple(sorted(tuple(p[a] for a in s) for s in S)) for p in ps)
    current={((),):1};levels=[1]
    for i in range(n):
        nxt=defaultdict(int)
        for S,c in current.items():
            for a in range(q):
                T=frozenset(s for s in step(S,a) if len(s)<=n-i-1)
                if T:nxt[canon(T)]+=c
        if len(nxt)>cap:raise RuntimeError('state cap exceeded')
        current=nxt;levels.append(len(current))
    return sum(c for S,c in current.items() if () in S),levels

def proper(w):return all(a!=b for a,b in zip(w,w[1:]))

def weighted_totals(q,n):
    """Distance transfer for the SUM OF WITNESS MULTIPLICITIES."""
    cur=[1]+[0]*n;out=[1]
    for _ in range(n):
        nxt=[0]*(n+1)
        for d,c in enumerate(cur):
            if d==0:
                if n:nxt[1]+=q*c
            else:
                nxt[d-1]+=c
                nxt[d]+=c
                if d<n:nxt[d+1]+=(q-1)*c
        cur=nxt;out.append(cur[0])
    return out
