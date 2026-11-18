#!/usr/bin/env python3
"""W_n(q) for EVERY alphabet size q: n <= 19 from binary and ternary data only;
n = 20 additionally from the single published term W_20(4) (OEIS A065237).

Inputs
  * W_n(1) (trivial), W_n(2) by brute force here, W_n(3) from the repository's
    exact counts (research/global_fusion_20261101, equal to OEIS A035617 n<=25).
Theorems used (PROVED-LEAN, run 41029475200, PR #42 / LabeledConnectedExpansion PR #34)
  * labeledWinningCount_connected_expansion: W_n(q) = sum over noncrossing pi of
    prod over blocks kappa_|B|(q), kappa_s(q) := connectedGameWeight q s,
    i.e. kappa are the free cumulants of the moment sequence W_.(q).
  * connectedGamePolynomial_eval / _natDegree_le / ConnectedCoefficientInterpolation:
    kappa_s(q) is an integer polynomial in q with zero constant term and
    degree <= max(1, s/5).
Hence for s <= 19 kappa_s has degree <= 3 and is fixed by its values at q = 1,2,3,
which are the free cumulants of the binary/ternary moment sequences. Re-assembling
moments gives W_n(q) for all q, n <= 19.
Independent checks: brute force for q = 4 (n <= 11) and q = 5 (n <= 9), and the
OEIS terms of A065238 (q=5), A065239 (q=6), A065241 (q=8) quoted below.
Output: JSON with kappa_s(q) and W_n(q) as exact integer-valued polynomials.
"""
import itertools, json, sys
from fractions import Fraction as F
from functools import lru_cache

N = 20
W3 = [1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,
      6103743,18624693,56870385,173760513,531128349]
A065237 = [1,0,4,4,28,64,268,844,3100,10876,39244,142432,518380,1906012,7012660,
           25980940,96407356,359260936,1341482740,5023006444,18844637356]   # q=4, n<=20
OEIS = {  # independent published terms, offset 0
 4: A065237[:20],                                                        # check only n<=19
 5: [1,0,5,5,45,105,545,1825,7965,30845,128945,527785,2202785,9222985,38818505,
     164436125,698347645,2981306665,12756855065],                       # A065238
 6: [1,0,6,6,66,156,966,3366,16986,70386,332646,1484676,6922146,31921506,
     149341506,700002366,3299514906,15618721956,74169285366],             # A065239
 8: [1,0,8,8,120,288,2360,8632,55224,249656,1443128,7243552,40366040,213357880,
     1178216264,6395922296,35375108728,194951335888],                    # A065241
}

@lru_cache(maxsize=None)
def win(rs):
    if not rs: return True
    for k, (c, n) in enumerate(rs):
        if n >= 2:
            L, R = rs[:k], rs[k+1:]
            nr = L[:-1] + ((L[-1][0], 2),) + R[1:] if (L and R and L[-1][0] == R[0][0]) else L + R
            if win(nr): return True
    return False

def runs(w):
    o = []
    for c in w:
        if o and o[-1][0] == c: o[-1][1] = 2
        else: o.append([c, 1])
    return tuple(map(tuple, o))

def brute(n, q):
    if n == 0: return 1
    return q * sum(win(runs((0,) + w)) for w in itertools.product(range(q), repeat=n - 1))

def powers(m, upto):
    """M^s coefficient lists for s = 0..upto (M truncated at len(m))."""
    n = len(m) - 1; out = [[F(1)] + [F(0)] * n]
    for _ in range(upto):
        p = out[-1]; out.append([sum(p[i] * m[j - i] for i in range(j + 1)) for j in range(n + 1)])
    return out

def cumulants(m):
    """Free cumulants from moments: m_t = sum_{s=1}^t kappa_s [z^{t-s}] M(z)^s."""
    n = len(m) - 1; P = powers([F(x) for x in m], n); k = [F(0)] * (n + 1)
    for t in range(1, n + 1):
        k[t] = m[t] - sum(k[s] * P[s][t - s] for s in range(1, t))
    return k

def moments(k, n):
    m = [F(1)] + [F(0)] * n
    for t in range(1, n + 1):
        P = powers(m, t)            # uses m[0..t-1]; m[t] still 0 and enters only via s=0 term
        m[t] = sum(k[s] * P[s][t - s] for s in range(1, t + 1))
    return m

def interp(points):
    """Exact monomial coefficients of the interpolating polynomial."""
    poly = [F(0)] * len(points)
    for i, (xi, yi) in enumerate(points):
        basis = [F(1)]; den = F(1)
        for j, (xj, _) in enumerate(points):
            if j == i: continue
            basis = [F(0)] + basis
            for d in range(len(basis) - 1): basis[d] -= xj * basis[d + 1]
            den *= xi - xj
        for d, c in enumerate(basis): poly[d] += yi * c / den
    while len(poly) > 1 and poly[-1] == 0: poly.pop()
    return poly

def ev(p, x): return sum(c * x**d for d, c in enumerate(p))

if __name__ == '__main__':
    W = {1: [1, 0] + [1] * (N - 1), 2: [brute(n, 2) for n in range(N + 1)], 3: W3}
    K = {q: cumulants(W[q]) for q in (1, 2, 3)}
    K[4] = cumulants(A065237)     # used ONLY for kappa_20 (needs a 4th point); n<=19 never uses it
    kpoly = {}
    for s in range(1, N + 1):
        qs = (1, 2, 3) if s <= 19 else (1, 2, 3, 4)          # s = 20 has degree <= 4
        p = interp([(0, F(0))] + [(q, K[q][s]) for q in qs])
        assert len(p) - 1 <= max(1, s // 5), (s, p)          # consistent with the Lean degree bound
        kpoly[s] = p
    def Wq(q):
        return moments([F(0)] + [ev(kpoly[s], q) for s in range(1, N + 1)], N)
    vals = {q: Wq(q) for q in range(0, 16)}
    for q in vals: assert all(x.denominator == 1 for x in vals[q])
    for q in (1, 2, 3): assert [int(x) for x in vals[q]] == W[q]
    for n in range(12): assert vals[4][n] == brute(n, 4), ('brute q=4', n)
    for n in range(10): assert vals[5][n] == brute(n, 5), ('brute q=5', n)
    for q, terms in OEIS.items():
        assert [int(x) for x in vals[q][:len(terms)]] == terms, ('OEIS', q)
    wpoly = {}
    for n in range(N + 1):
        p = interp([(q, vals[q][n]) for q in range(0, 12)])
        assert all(ev(p, q) == vals[q][n] for q in range(12, 16))
        assert len(p) - 1 <= n // 2 or n == 0
        wpoly[n] = p
    s = lambda p: [str(c) for c in p]
    print(json.dumps({
        'status': 'PASS',
        'checks': ['binary/ternary reproduced', 'brute force q=4 n<=11, q=5 n<=9',
                   'OEIS A065237 (q=4) n<=19, A065238 (q=5) n<=18, A065239 (q=6) n<=18, A065241 (q=8) n<=17'],
        'kappa_s_coefficients_in_q_low_to_high': {s_: s(p) for s_, p in kpoly.items()},
        'W_n_coefficients_in_q_low_to_high': {n: s(p) for n, p in wpoly.items()},
        'W_19_by_q': {q: int(vals[q][19]) for q in range(1, 16)},
        'W_18_by_q': {q: int(vals[q][18]) for q in range(1, 16)},
        'W_20_by_q': {q: int(vals[q][20]) for q in range(1, 16)},
        'note_n20': 'n=20 additionally uses the published A065237 term W_20(4)=18844637356 (Dobbelaere/Kurz data).',
    }, indent=1))
