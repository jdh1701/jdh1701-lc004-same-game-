"""General formula: winning patterns with rigid classes (m2 pairs, m3 triples) and
big classes of sizes s_1..s_r (>=4).
  W = w!/(b*m2!*m3!) * C(n, k-r) * [z^s] Omega(z)^b / prod(mult of sizes)!
with w=m2+m3, N0 = 2m2+3m3, b = N0+1-w, n = N0+sum s, k = w+r,
Omega(z) = sum over winning words on r labelled letters of z^content."""
import sys, itertools
from math import comb, factorial
from functools import lru_cache
from collections import Counter
sys.setrecursionlimit(100000)

@lru_cache(None)
def cert(w):
    n=len(w)
    if n==0: return True
    c=w[0]
    for j in range(1,n):
        if w[j]==c and cert(w[1:j]):
            if cert(w[j+1:]): return True
            for l in range(j+1,n):
                if w[l]==c and cert(w[j+1:l]) and cert(w[l+1:]): return True
    return False

@lru_cache(None)
def omega_content(content):
    """number of winning words with exactly this letter-content vector (labelled letters)."""
    letters=[i for i,c in enumerate(content) for _ in range(c)]
    if any(c==1 for c in content): return 0
    cnt=0
    for perm in multiset_perms(list(content)):
        if cert(perm): cnt+=1
    cert.cache_clear()
    return cnt

def multiset_perms(counts):
    n=sum(counts); w=[0]*n
    def rec(i):
        if i==n:
            yield tuple(w); return
        for c in range(len(counts)):
            if counts[c]:
                counts[c]-=1; w[i]=c
                yield from rec(i+1)
                counts[c]+=1
    yield from rec(0)

def omega_power_coeff(s, b):
    """[z^s] Omega^b computed as sum_t C(b,t) [z^s](Omega-1)^t."""
    s=tuple(s); r=len(s)
    # all nonzero content vectors <= s
    vecs=[v for v in itertools.product(*[range(x+1) for x in s]) if any(v)]
    om={v:omega_content(v) for v in vecs}
    om={v:x for v,x in om.items() if x}
    # dp over t
    cur={tuple([0]*r):1}; total=0; t=0
    while cur:
        if tuple(s) in cur: total+=comb(b,t)*cur[tuple(s)]
        nxt={}
        for v,x in cur.items():
            for u,y in om.items():
                wv=tuple(a+c for a,c in zip(v,u))
                if all(a<=c for a,c in zip(wv,s)):
                    nxt[wv]=nxt.get(wv,0)+x*y
        cur=nxt; t+=1
    return total

def W_general(big, m2, m3):
    r=len(big); w=m2+m3; N0=2*m2+3*m3; b=N0+1-w
    n=N0+sum(big); k=w+r
    sym=1
    for v in Counter(big).values(): sym*=factorial(v)
    if w==0:
        # no rigid classes: whole circle is one face, answer = winning words count / sym
        return omega_content(tuple(big))//sym
    num=factorial(w)*comb(n,k-r)*omega_power_coeff(big,b)
    den=b*factorial(m2)*factorial(m3)*sym
    assert num%den==0, (big,m2,m3,num,den)
    return num//den

if __name__=="__main__":
    sys.path.insert(0,'.')
    from profile import per_profile
    for j in range(2,6):
        pp=per_profile(j,6)
        for prof,ser in sorted(pp.items()):
            big=[x for x in prof if x>=4]; m3=sum(1 for x in prof if x==3)
            if not big: continue
            got=[W_general(big,N,m3) for N in range(0,7)]
            print(prof, got==ser, got[:4], ser[:4], flush=True)
