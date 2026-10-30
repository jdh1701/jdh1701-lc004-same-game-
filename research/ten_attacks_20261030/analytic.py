"""Attack1: exact low-complexity ansatz elimination, standard-library arithmetic.
OEIS A035617 retrieved2026-10-30. A fitted identity is never a proof.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
A=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503]
N=len(A)
def rref(M):
    M=[list(map(Q,r)) for r in M];piv=[];r=0
    for c in range(len(M[0])):
        k=next((i for i in range(r,len(M)) if M[i][c]),None)
        if k is None:continue
        M[r],M[k]=M[k],M[r];f=M[r][c];M[r]=[x/f for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]:
                f=M[i][c];M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c);r+=1
        if r==len(M):break
    return M,piv

def nullspace(M):
    R,p=rref(M);out=[]
    for c in range(len(M[0])):
        if c in p:continue
        v=[Q(0)]*len(M[0]);v[c]=Q(1)
        for i,j in enumerate(p):v[j]=-R[i][c]
        out.append(v)
    return out

def conv(a,b):return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(N)]
powers=[[1]+[0]*(N-1),A]
for j in range(2,6):powers.append(conv(powers[-1],A))
checks=[]
for dy in range(1,6):
    for dx in range(9):
        terms=[(i,j) for j in range(dy+1) for i in range(dx+1)]
        if len(terms)>20:continue
        M=[[powers[j][k-i] if k>=i else 0 for i,j in terms] for k in range(N)]
        train=nullspace(M[:20]);full=nullspace(M)
        checks.append(dict(kind='algebraic',degree_y=dy,degree_x=dx,unknowns=len(terms),training_kernel=len(train),full_kernel=len(full),heldout_residuals=[[str(sum(x*y for x,y in zip(row,v))) for row in M[20:]] for v in train]))
for order in range(1,9):
    for degree in range(4):
        terms=[(j,k) for j in range(order+1) for k in range(degree+1)]
        if len(terms)>N-order-5:continue
        M=[[n**k*A[n+j] for j,k in terms] for n in range(N-order)]
        split=N-order-5;train=nullspace(M[:split]);full=nullspace(M)
        checks.append(dict(kind='P_recursive',order=order,degree=degree,unknowns=len(terms),training_kernel=len(train),full_kernel=len(full)))
M=[[A[n-j] for j in range(1,11)]+[A[n]] for n in range(10,20)]
R,piv=rref(M);assert piv==list(range(10));c=[r[-1] for r in R]
fail=[]
for n in range(20,N):
    pred=sum(c[j-1]*A[n-j] for j in range(1,11))
    if pred!=A[n]:fail.append(dict(n=n,prediction=str(pred),actual=A[n]))
out=dict(status='VERIFIED-COMP',source='https://oeis.org/A035617',terms=A,training_length=20,checks=checks,order10_coefficients=list(map(str,c)),order10_holdout_failures=fail)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('exact ansatz spaces',len(checks),'survivors',sum(bool(c['full_kernel']) for c in checks),'order10 first holdout',fail[:1])
