"""Independent exhaustive RGS-pattern Same Game comparison.
No use of the grammar solver in the reference winning predicate.
"""
from collections import defaultdict
from functools import lru_cache
from rgs_symbolic_count import coefficient_counts,winning_polynomial_value

@lru_cache(None)
def maximal_run_win(w):
    if not w:return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[i]==w[j]:j+=1
        if j-i>=2 and maximal_run_win(w[:i]+w[j:]):return True
        i=j
    return False

def canonical_patterns(n,Q):
    def recur(w,k):
        if len(w)==n:
            yield w,k
        else:
            for a in range(min(k+1,Q)):
                yield from recur(w+(a,),max(k,a+1))
    yield from recur((),0)

for n in range(2,11):
    Q=n//2
    actual=defaultdict(int)
    for w,k in canonical_patterns(n,Q):
        if maximal_run_win(w):actual[k]+=1
    got,levels,cache=coefficient_counts(Q,n)
    assert got==dict(sorted(actual.items())),(n,got,dict(actual))
    print('PASS original game vs symbolic grammar',n,got,flush=True)

known={8:879,10:7833,12:71385,13:216765,14:657849,15:2003151}
for n,expected in known.items():
    coeff,levels,_=coefficient_counts(n//2,n)
    actual=winning_polynomial_value(coeff,3)
    assert actual==expected,(n,actual,expected)
    print('PASS published ternary count',n,actual,'peak_states',max(levels),flush=True)
print('ALL RGS SYMBOLIC CHECKS PASSED')
