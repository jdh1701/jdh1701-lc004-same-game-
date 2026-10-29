# Single big class formula via Tutte bicoloured-tree count.
from fractions import Fraction as F
from math import factorial, comb
import sys
sys.path.insert(0,'.')
def H(d, s):  # coefficients in y up to y^s of (1-y)^{-d} - d*y
    return [comb(t+d-1, d-1) - (d if t==1 else 0) for t in range(s+1)]
def ymul(a,b,s):
    c=[0]*(s+1)
    for i,x in enumerate(a):
        if x:
            for j,yv in enumerate(b[:s+1-i]): c[i+j]+=x*yv
    return c
def W_single(s, m2, m3):
    """# winning patterns: one class of size s>=4, m2 pairs, m3 triples."""
    N0 = 2*m2 + 3*m3; w = m2 + m3; b = N0 + 1 - w
    # bivariate series in u (deg N0) with y-poly coefficients (deg s)
    S = [[0]*(s+1)] + [H(d, s) for d in range(1, N0+1)]           # S[d] = H_d
    D = [[0]*(s+1)] + [[d*x for x in H(d+1, s)] for d in range(1, N0+1)]
    def umul(A,B):
        C=[[0]*(s+1) for _ in range(N0+1)]
        for i in range(N0+1):
            if not any(A[i]): continue
            for j in range(N0+1-i):
                if not any(B[j]): continue
                p=ymul(A[i],B[j],s)
                for t in range(s+1): C[i+j][t]+=p[t]
        return C
    P = D
    for _ in range(b-1): P = umul(P, S)
    coeff = P[N0][s]
    num = factorial(w-1) * coeff if w>=1 else coeff
    den = factorial(m2)*factorial(m3)
    assert num % den == 0
    return num//den
if __name__=="__main__":
    from templates import diagonal_mobius
    import json
    # compare with brute force table rows
    from math import factorial as f
    # brute force: patterns with one class of size s and rest pairs/triples: use per-profile template
    from profile import per_profile
    for j in (2,3,4,5):
        pp = per_profile(j, 8)
        for prof, ser in sorted(pp.items()):
            big=[x for x in prof if x>=4]
            if len(big)!=1: continue
            s=big[0]; m3=sum(1 for x in prof if x==3)
            ok=all(W_single(s,N,m3)==ser[N] for N in range(0 if m3 else 1, 9))
            print(prof, ok, [W_single(s,N,m3) for N in range(1,5)], ser[1:5])
