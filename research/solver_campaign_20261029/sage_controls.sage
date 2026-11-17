# Independent SageMath controls; exact arithmetic throughout.
import json
from functools import lru_cache
from sage.version import version as sage_version
print(sage_version)
R.<k> = PolynomialRing(QQ)
f=(38*k^6+694*k^5+4025*k^4+6670*k^3-5593*k^2-9434*k+6840)/(360*(k+8))
lead=f.numerator().leading_coefficient()/f.denominator().leading_coefficient()
res=((k+8)*f)(-8)
assert lead == QQ(19)/180 and res == 45
@lru_cache(None)
def win(w):
    if not w: return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]: j+=1
        if j-i>=2 and win(w[:i]+w[j:]): return True
        i=j
    return False
# Target crossed (4,4) partition, 0,1,4,5 vs 2,3,6,7.
blocks=[[0,1,4,5],[2,3,6,7]]
parts=list(SetPartitions(4)); coefficient=ZZ(0); tested=0
for A in parts:
    for B in parts:
        w=[None]*8
        for offset,(positions,pi) in enumerate(zip(blocks,[A,B])):
            for j,block in enumerate(pi):
                for i in block: w[positions[i-1]]=offset*4+j
        # mu(pi,top) depends only on the number of its blocks.
        muA=(-1)^(len(A)-1)*factorial(len(A)-1)
        muB=(-1)^(len(B)-1)*factorial(len(B)-1)
        coefficient += muA*muB*ZZ(win(tuple(w)));tested+=1
assert coefficient==0 and tested==225
print(json.dumps({'R6_leading':str(lead),'R6_residue_at_minus8':str(res),'crossed44_coefficient':int(coefficient),'refinements':int(tested)}))
