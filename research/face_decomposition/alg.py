import sys; sys.path.insert(0,'.')
from guess import W3, solve
from fractions import Fraction as F
N=len(W3)
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i): c[i+j]+=x*b[j]
    return c
f=W3[:]
pw=[[1]+[0]*(N-1)]
for d in range(1,5): pw.append(mul(pw[-1],f))
for d in range(1,5):
    for e in range(0,12):
        unk=(d+1)*(e+1)
        if unk > N-3: break
        # columns: x^i * f^p ; equations: coefficient of x^m, m < N
        cols=[]
        for p in range(d+1):
            for i in range(e+1):
                cols.append([0]*i+pw[p][:N-i])
        eqs=[[cols[c][m] for c in range(unk)] for m in range(N)]
        ns=solve(eqs)
        if ns:
            print(f"algebraic candidate: deg_f={d}, deg_x={e}, unknowns={unk}, eqs={N}, nullity={len(ns)}"); sys.exit()
print("no algebraic equation P(x,f)=0 with deg_f<=4 and (deg_f+1)(deg_x+1) <= 23 for 3-colour series")
