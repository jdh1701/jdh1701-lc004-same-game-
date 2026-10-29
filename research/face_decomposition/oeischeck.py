import sys,time; sys.path.insert(0,'.')
from diag_formula import W, big_partitions
from guess import W3
def fib(n):
    a,b=0,1
    for _ in range(n): a,b=b,a+b
    return a
data={3:W3,
4:[1,0,4,4,28,64,268,844,3100,10876,39244,142432,518380,1906012,7012660,25980940,96407356,359260936,1341482740,5023006444,18844637356],
5:[1,0,5,5,45,105,545,1825,7965,30845,128945,527785,2202785,9222985,38818505,164436125,698347645,2981306665,12756855065],
6:[1,0,6,6,66,156,966,3366,16986,70386,332646,1484676,6922146,31921506,149341506,700002366,3299514906,15618721956,74169285366],
7:[1,0,7,7,91,217,1561,5593,32011,139363,732697,3492265,17899609,89014933,455041825,2311847083,11875575355,61080825757],
8:[1,0,8,8,120,288,2360,8632,55224,249656,1443128,7243552,40366040,213357880,1178216264,6395922296,35375108728,194951335888],
9:[1,0,9,9,153,369,3393,12609,89145,415161,2614689,13684977,82237185,457154577,2704775985,15524314425,91659251961],
10:[1,0,10,10,190,460,4690,17650,136630,651790,4439890,24056020,154885870,898393870,5659321510,34068918250,213351643990]}
def Wq(n,q):
    if q==1: return 1 if n!=1 else 0
    if q==2: return 2**n-2*n*fib(n-2)-(-1)**n-1
    return data[q][n]
def ff(q,k):
    r=1
    for i in range(k): r*=q-i
    return r
def A(n,k):
    j=n-2*k; return sum(W(list(big),k-len(big)-m3,m3) for m3 in range(j+1) for big in big_partitions(j-m3) if k-len(big)-m3>=0)
if False:
    t=time.time()
    row=[A(n,k) for k in range(1,n//2+1)]
    # predicted W_n(q) for each q with data
    res=[]
    for q in range(2,11):
        if q>2 and n>=len(data[q]): continue
        pred=sum(row[k-1]*ff(q,k) for k in range(1,n//2+1))
        res.append((q, pred==Wq(n,q)))
    print(n,row,res,f"{time.time()-t:.0f}s",flush=True)
import json
from fractions import Fraction as Fr
diag=json.load(open('diag_formula.json'))
for n in (16,17):
    kmax=n//2
    # solve W_n(q)=sum_k A(n,k) q^(k) for q=1..kmax (lower triangular in falling factorials)
    Aq=[None]*(kmax+1)
    for q in range(1,kmax+1):
        s=Wq(n,q)-sum(Aq[k]*ff(q,k) for k in range(1,q))
        assert s % ff(q,q)==0
        Aq[q]=s//ff(q,q)
    out=[]
    for k in range(1,kmax+1):
        j=n-2*k
        th = diag[str(j)][str(k)] if str(j) in diag else None
        if j==0:
            from math import comb; th=comb(2*k,k)//(k+1)
        out.append((k,j,Aq[k],th,'OK' if th==Aq[k] else ('-' if th is None else 'MISMATCH')))
    print(n,out)
    # extra: q=10 consistency for n=16
    if n==16: print(' q=10 check:', sum(Aq[k]*ff(10,k) for k in range(1,kmax+1))==Wq(16,10))
