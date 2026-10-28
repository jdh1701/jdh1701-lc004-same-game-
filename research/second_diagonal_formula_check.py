"""Test second-from-maximal-color diagonal of Same Game grammar coefficients.
Conjecture (k>=2): a(2k+2,k) = binom(k+1,2)*Catalan(k+1)
 - binom(2k+2,k-1)
 + (2k+2)! / [2*(k-2)!*(k+3)!].
This tests known independently computed coefficients and produces held-out predictions.
It does not prove the formula or original-game/grammar equivalence.
"""
from math import comb, factorial

def catalan(n):return comb(2*n,n)//(n+1)
def predicted_four(k):
    return comb(k+1,2)*catalan(k+1)-comb(2*k+2,k-1)
def predicted_two_triples(k):
    n=2*k+2
    return factorial(n)//(2*factorial(k-2)*factorial(k+3))
def predicted(k):return predicted_four(k)+predicted_two_triples(k)

# Coefficients independently obtained via RGS symbolic grammar counter.
known={2:12,3:84,4:480,5:2475,6:12012}
for k,value in known.items():
    got=predicted(k)
    assert got==value,(k,got,value)
    print('PASS',k,'length',2*k+2,'four-occurrence',predicted_four(k),
          'two-triples',predicted_two_triples(k),'total',got)
for k in (7,8,9):
    print('UNVERIFIED PREDICTION',k,'length',2*k+2,'total',predicted(k))
