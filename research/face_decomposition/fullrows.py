import sys,time; sys.path.insert(0,'.')
from diag_formula import W, big_partitions
def A(n,k):
    j=n-2*k; return sum(W(list(big),k-len(big)-m3,m3) for m3 in range(j+1) for big in big_partitions(j-m3) if k-len(big)-m3>=0)
bf={11:[1,649,3300,2310,330],12:[1,1386,10511,10395,2475,132],13:[1,2938,33189,44759,15015,1287],14:[1,6174,103467,185640,85085,12012,429]}
for n in range(4,15):
    t=time.time(); row=[A(n,k) for k in range(1,n//2+1)]
    print(n,row, 'BF-match' if n not in bf else row==bf[n], f"{time.time()-t:.1f}s",flush=True)
