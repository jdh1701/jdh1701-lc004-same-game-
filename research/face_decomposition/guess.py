from fractions import Fraction as F
W3=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503]
def fib(n):
    a,b=0,1
    for _ in range(n): a,b=b,a+b
    return a
A2=[0]*26; A3=[0]*26
for n in range(2,26):
    W2=2**n-2*n*fib(n-2)-(-1)**n-1
    A2[n]=(W2-2)//2
    A3[n]=(W3[n]-3-6*A2[n])//6
    assert 3+6*A2[n]+6*A3[n]==W3[n]
print("A(n,2):",A2[2:16]); print("A(n,3):",A3)
def solve(M,rhs=None):
    # nullspace of M (rows) over Q via gaussian elimination
    M=[[F(x) for x in r] for r in M]; rows=len(M); cols=len(M[0]); piv=[]; r=0
    for c in range(cols):
        p=next((i for i in range(r,rows) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==rows: break
    free=[c for c in range(cols) if c not in piv]
    sols=[]
    for fc in free:
        v=[F(0)]*cols; v[fc]=F(1)
        for i,pc in enumerate(piv): v[pc]=-M[i][fc]
        sols.append(v)
    return sols
seq=A3
start=6
found=False
for order in range(1,8):
    for deg in range(0,8):
        unk=(order+1)*(deg+1)
        eqs=[]
        for n in range(start+order, 26):
            eqs.append([ (n**d)*seq[n-i] for i in range(order+1) for d in range(deg+1)])
        if len(eqs) < unk+3: continue
        ns=solve(eqs)
        if len(ns)>=1:
            print(f"P-recursive candidate: order {order}, degree {deg}, unknowns {unk}, equations {len(eqs)}, nullity {len(ns)}")
            found=True; break
    if found: break
if not found: print("no P-recursive recurrence with order<=7, deg<=7 fitting n>=",start,"(with >=3 spare equations)")
