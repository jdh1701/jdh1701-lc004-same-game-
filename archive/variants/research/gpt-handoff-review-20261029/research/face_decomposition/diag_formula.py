import sys, json, itertools, time
sys.path.insert(0,'.')
from general import omega_content
from math import comb, factorial
from collections import Counter
from functools import lru_cache

@lru_cache(None)
def omega_t_coeffs(s):
    """c_t = [z^s](Omega-1)^t for t=0.. ; returns list."""
    r=len(s)
    vecs=[v for v in itertools.product(*[range(x+1) for x in s]) if any(v)]
    om={v:omega_content(v) for v in vecs}; om={v:x for v,x in om.items() if x}
    cur={tuple([0]*r):1}; res=[]
    while cur:
        res.append(cur.get(tuple(s),0))
        nxt={}
        for v,x in cur.items():
            for u,y in om.items():
                wv=tuple(a+c for a,c in zip(v,u))
                if all(a<=c for a,c in zip(wv,s)): nxt[wv]=nxt.get(wv,0)+x*y
        cur=nxt
    return res

def big_partitions(e):
    """multisets of sizes>=4 with sum(s-2)=e"""
    out=[]
    def rec(rem,mx,acc):
        if rem==0: out.append(tuple(acc)); return
        for s in range(min(mx,rem+2),3,-1): rec(rem-(s-2),s,acc+[s])
    rec(e,e+2,[]); return out

def W(big, m2, m3):
    r=len(big); w=m2+m3; N0=2*m2+3*m3; n=N0+sum(big)
    sym=1
    for v in Counter(big).values(): sym*=factorial(v)
    if w==0: return omega_content(tuple(big))//sym
    b=N0+1-w
    P=sum(comb(b,t)*c for t,c in enumerate(omega_t_coeffs(tuple(big))))
    num=factorial(n)*P; den=factorial(n-w)*factorial(m2)*factorial(m3)*b*sym
    assert num%den==0
    return num//den

def A_diag(j,k):
    tot=0
    for m3 in range(0,j+1):
        for big in big_partitions(j-m3):
            r=len(big); m2=k-r-m3
            if m2<0: continue
            tot+=W(list(big),m2,m3)
    return tot

if __name__=="__main__":
    J=int(sys.argv[1]); K=int(sys.argv[2])
    res={}
    for j in range(1,J+1):
        t=time.time()
        res[str(j)]={str(k):A_diag(j,k) for k in range(1,K+1)}
        print(j,[res[str(j)][str(k)] for k in range(1,8)],f"{time.time()-t:.1f}s",flush=True)
        json.dump(res,open('diag_formula.json','w'))
