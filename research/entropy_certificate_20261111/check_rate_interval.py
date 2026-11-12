"""Rigorous rational enclosure of exp(entropy), no floating point/log library."""
from fractions import Fraction as F
import json

def log_interval(x, terms=12):
    assert x>1
    z=(x-1)/(x+1)
    lower=2*sum((z**(2*k+1)/F(2*k+1) for k in range(terms)),F(0))
    tail=2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
    return lower,lower+tail
H=111028731;L=100000000;D=H+2*L
low=F('2.99627261278230836');high=F('2.99627261278230838')
factor=F(H,D)
b0,b1=log_interval(F(H,L))
a0,a1=log_interval(F(D,L)/low)
c0,c1=log_interval(F(D,L)/high)
assert a0>factor*b1
assert c1<factor*b0
print(json.dumps({'status':'PASS','strict_lower_bound':'2.99627261278230836',
 'strict_upper_bound':'2.99627261278230838','terms':12,
 'method':'Exact rational atanh-series logarithm bounds; positive geometric tail bound; no floating point.'},indent=2))
