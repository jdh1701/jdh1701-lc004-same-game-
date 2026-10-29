import json,sys
from fractions import Fraction as F
from math import comb
def interp(pts):
    # Newton -> monomial coeffs
    n=len(pts); xs=[F(p[0]) for p in pts]; coef=[F(p[1]) for p in pts]
    for j in range(1,n):
        for i in range(n-1,j-1,-1):
            coef[i]=(coef[i]-coef[i-1])/(xs[i]-xs[i-j])
    poly=[F(0)]*n
    for i in range(n-1,-1,-1):
        # poly = poly*(x-xs[i]) + coef[i]
        new=[F(0)]*n
        for a in range(n-1):
            new[a+1]+=poly[a]
        for a in range(n):
            new[a]-=xs[i]*poly[a]
        new[0]+=coef[i]; poly=new
    return poly
def ev(p,x): return sum(c*x**i for i,c in enumerate(p))
def roots(p):
    # rational roots among small halves/thirds
    r=[]
    for den in (1,2,3,4,6):
        for num in range(-60,61):
            x=F(num,den)
            if x not in r and ev(p,x)==0: r.append(x)
    return r
def show(p):
    return " + ".join(f"({c})k^{i}" for i,c in enumerate(p) if c)
if __name__=="__main__":
    d=json.load(open(sys.argv[1] if len(sys.argv)>1 else 'diag.json'))
    for j in sorted(d,key=int):
        jj=int(j); vals={int(a):b for a,b in d[j].items()}; ks=sorted(vals)
        ratio={x:F(vals[x],comb(2*x+jj,x-1)) for x in ks}
        for deg in range(0,len(ks)-2):
            p=interp([(x,ratio[x]) for x in ks[:deg+1]])
            if all(ev(p,x)==ratio[x] for x in ks):
                while p and p[-1]==0: p.pop()
                print(f"j={jj} deg={len(p)-1} lead={p[-1]} roots={[str(x) for x in roots(p)]}  ({len(ks)} pts)")
                print("   ",show(p)); break
        else: print(j,"no fit")
