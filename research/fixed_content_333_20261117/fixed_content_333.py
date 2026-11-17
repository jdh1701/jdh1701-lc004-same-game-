#!/usr/bin/env python3
"""Exact fixed-content counts W(3,3,r): labeled words with three A's, three B's
and r C's that can be erased completely under maximal-run deletion.

Two independent methods, standard library only:
  brute  - enumerate every word, solve the game by memoized search on runs.
  types  - the game depends on each run length only through min(len,2), and
           this cap is preserved when runs merge. So a word is determined, for
           the game, by its A/B pattern (20 choices) and the type of each of its
           7 C-gaps in {0, 1, 2+}. A type vector with s gaps of size 1 and k gaps
           of size >= 2 is realized by C(r-s-k-1, k-1) gap vectors when k >= 1,
           and by [r == s] when k = 0.

Consequence (proved by the types formula): for r >= 8, every binomial
C(r-s-k-1, k-1) is a polynomial in r (its top argument is >= 0 since
s+k <= 7), so W(3,3,r) agrees with one polynomial of degree <= 6 for all r >= 8.
The script derives it by exact interpolation and checks it.

Usage: python3 fixed_content_333.py [brute_max_r=11] [types_max_r=40]
"""
import itertools, json, sys
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd

def runs(w):
    out = []
    for c in w:
        if out and out[-1][0] == c: out[-1][1] += 1
        else: out.append([c, 1])
    return tuple((c, min(n, 2)) for c, n in out)   # cap is exact, see docstring

@lru_cache(maxsize=None)
def win(rs):
    if not rs: return True
    for k, (c, n) in enumerate(rs):
        if n >= 2:
            L, R = rs[:k], rs[k+1:]
            if L and R and L[-1][0] == R[0][0]:
                nr = L[:-1] + ((L[-1][0], min(L[-1][1] + R[0][1], 2)),) + R[1:]
            else:
                nr = L + R
            if win(nr): return True
    return False

def win_uncapped(w):
    """Independent solver with no length cap, for the brute-force method."""
    @lru_cache(maxsize=None)
    def go(s):
        if not s: return True
        i = 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]: j += 1
            if j - i >= 2 and go(s[:i] + s[j:]): return True
            i = j
        return False
    return go(w)

PATTERNS = sorted(set(itertools.permutations('AAABBB')))   # 20

def brute(r):
    total = 0
    for pat in PATTERNS:
        for cut in itertools.combinations(range(r + 6), 6):   # positions of A/B letters
            w = ['C'] * (r + 6)
            for pos, ch in zip(cut, pat): w[pos] = ch
            total += win_uncapped(''.join(w))
    return total

def types_count(r):
    total = 0
    for pat in PATTERNS:
        for t in itertools.product((0, 1, 2), repeat=7):
            s, k = t.count(1), t.count(2)
            if k == 0: mult = 1 if r == s else 0
            else:
                n = r - s - k - 1
                mult = comb(n, k - 1) if n >= 0 else 0
            if not mult: continue
            w = []
            for g, ch in zip(t, pat + ('',)):
                w += [('C', g)] if g else []
                if ch: w.append((ch, 1))
            merged = []
            for c, n in w:
                if merged and merged[-1][0] == c: merged[-1] = (c, min(merged[-1][1] + n, 2))
                else: merged.append((c, n))
            if win(tuple(merged)): total += mult
    return total

def interpolate(points):
    """Exact Newton coefficients -> monomial coefficients (Fractions)."""
    xs = [x for x, _ in points]; coef = [F(y) for _, y in points]
    for j in range(1, len(xs)):
        for i in range(len(xs) - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i-1]) / (xs[i] - xs[i-j])
    # rebuild directly: sum coef[i] * prod_{j<i} (r - x_j)
    poly = [F(0)] * len(xs)
    for i, c in enumerate(coef):
        term = [F(1)]
        for x in xs[:i]:
            term = [F(0)] + term
            for d in range(len(term) - 1): term[d] -= x * term[d+1]
        for d, v in enumerate(term): poly[d] += c * v
    while len(poly) > 1 and poly[-1] == 0: poly.pop()
    return poly

def ev(poly, r): return sum(c * r**d for d, c in enumerate(poly))

if __name__ == '__main__':
    bmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    tmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    T = {r: types_count(r) for r in range(0, tmax + 1)}
    B = {r: brute(r) for r in range(0, bmax + 1)}
    assert all(B[r] == T[r] for r in B), 'methods disagree'
    poly = interpolate([(r, T[r]) for r in range(8, 15)])        # 7 points, degree <= 6
    assert all(ev(poly, r) == T[r] for r in range(8, tmax + 1)), 'polynomial fails'
    first = min(r for r in range(9) if all(ev(poly, x) == T[x] for x in range(r, 9)))
    old = {r: (2**(r-3) + 1) * (r + 6) * (r + 5) for r in range(3, tmax + 1)}
    den = 1
    for c in poly: den = den * c.denominator // gcd(den, c.denominator)
    out = {
        'status': 'PASS',
        'methods_agree_through_r': bmax,
        'counts': {r: T[r] for r in range(0, tmax + 1)},
        'polynomial_valid_from_r': first,
        'polynomial_times_%d_coefficients_low_to_high' % den: [int(c * den) for c in poly],
        'old_formula_matches_r': [r for r in old if old[r] == T[r]],
        'old_formula_at_7_8': [old[7], old[8]],
        'scope': 'Labeled words (colors A,B,C distinguishable), content exactly (3,3,r).',
    }
    print(json.dumps(out, indent=1))
