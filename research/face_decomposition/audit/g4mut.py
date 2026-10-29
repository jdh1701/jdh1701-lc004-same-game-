import sys; sys.path.insert(0,'..')
import diag_formula as D
from math import comb, factorial
from collections import Counter
BF={4:[1,2],5:[1,5],6:[1,12,5],7:[1,28,21],8:[1,62,84,14],9:[1,138,300,84],10:[1,300,1005,480,42],
    11:[1,649,3300,2310,330],12:[1,1386,10511,10395,2475,132]}
def make_W(mut):
    def W(big,m2,m3):
        r=len(big); w=m2+m3; N0=2*m2+3*m3; n=N0+sum(big)
        sym=1
        if mut!='M5':
            for v in Counter(big).values(): sym*=factorial(v)
        if w==0: return D.omega_content(tuple(big))//sym
        b=N0+1-w
        bb=b+1 if mut=='M3' else b
        coeffs=list(D.omega_t_coeffs(tuple(big)))
        P=sum(comb(bb,t)*c for t,c in enumerate(coeffs))
        if mut=='M2' and len(big)>0:  # allow singleton letters inside faces: crude extra term
            P+= bb*sum(1 for x in big if x==1)  # no-op guard
            P+= comb(bb,sum(big))  # each heavy point alone in its own face allowed
        num=factorial(n)*P; den=factorial(n-w)*factorial(m2)*factorial(m3)*b*sym
        if mut=='M1': den//=b
        if mut=='M4': den=factorial(n-w+1)*factorial(m2)*factorial(m3)*b*sym
        if mut=='M6': num=num*b; den=den*w
        return num/den
    return W
def row(n,Wf):
    out=[]
    for k in range(1,n//2+1):
        j=n-2*k; t=0
        for m3 in range(j+1):
            for big in D.big_partitions(j-m3):
                m2=k-len(big)-m3
                if m2>=0: t+=Wf(list(big),m2,m3)
        out.append(t)
    return out
results={}
for mut in ['none','M1','M2','M3','M4','M5','M6']:
    Wf=make_W(mut)
    bad=sum(1 for n,r in BF.items() for a,b in zip(row(n,Wf),r) if a!=b)
    results[mut]=bad
    print(mut,'mismatching entries:',bad, '(KILLED)' if (mut!='none' and bad>0) else ('(SURVIVED!)' if mut!='none' else '(baseline)'))
