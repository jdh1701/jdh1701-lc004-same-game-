#!/usr/bin/env python3
"""Binary content counts B(a,b): words with a A's and b B's that win under
maximal-run deletion (WORKBOARD H1). Same type-sum method as
fixed_content_333.py: by the cap lemma only gap types {0,1,2+} matter, and a
type with s ones and k>=1 "2+" gaps has C(b-s-k-1, k-1) realizations. For
b >= a+2 every such binomial is a polynomial in b, so B(a,.) is a polynomial
there; the all-"2+" type (k = a+1, a winning word for a >= 2) is the unique
degree-a term, so the degree is exactly a with leading coefficient 1/a!.
This script derives each polynomial, checks it through b = 4a+11, checks the
type sum against brute force for a+b <= 18, and reports the first b where the
polynomial holds. Usage: python3 binary_content.py [a_max=7]"""
import itertools, json, os, sys
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fixed_content_333 import win, win_uncapped, interpolate, ev

def B(a, b):
    tot = 0
    for t in itertools.product((0, 1, 2), repeat=a + 1):
        s, k = t.count(1), t.count(2)
        if k == 0: mult = 1 if b == s else 0
        else: mult = comb(b - s - k - 1, k - 1) if b - s - k - 1 >= 0 else 0
        if not mult: continue
        w = []
        for i, g in enumerate(t):
            if g: w.append(('B', g))
            if i < a:
                if w and w[-1][0] == 'A': w[-1] = ('A', 2)
                else: w.append(('A', 1))
        if win(tuple(w)): tot += mult
    return tot

def brute(a, b):
    return sum(win_uncapped(''.join('A' if i in c else 'B' for i in range(a + b)))
               for c in itertools.combinations(range(a + b), a))

if __name__ == '__main__':
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    out = {}
    for a in range(2, amax + 1):
        vals = {b: B(a, b) for b in range(0, 4 * a + 12)}
        for b in range(0, 19 - a):
            assert brute(a, b) == vals[b], (a, b)
        P = interpolate([(b, vals[b]) for b in range(a + 2, 2 * a + 3)])
        assert all(ev(P, b) == vals[b] for b in range(a + 2, 4 * a + 12))
        first = min(b for b in range(a + 3) if all(ev(P, x) == vals[x] for x in range(b, a + 3)))
        out[a] = {'degree': len(P) - 1, 'leading': str(P[-1]), 'valid_from_b': first,
                  'coefficients_low_to_high': [str(c) for c in P],
                  'values_b_0_to_' + str(4 * a + 11): [vals[b] for b in range(4 * a + 12)]}
    print(json.dumps({'status': 'PASS', 'by_a': out,
                      'note': 'B(1,b)=0 for all b (a single A can never be deleted).'}, indent=1))
