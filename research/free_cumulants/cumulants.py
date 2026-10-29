"""Exact free cumulants kappa_s(q) (polynomials in q) of the winning-word moment sequence T(q,n)."""
from math import factorial
from functools import lru_cache
rows = {}
for line in open("rows.txt"):
    n, vals = line.split(":"); rows[int(n)] = [int(v) for v in vals.split()]
@lru_cache(None)
def S2(j, k):
    if j == k: return 1
    if k == 0 or k > j: return 0
    return k * S2(j - 1, k) + S2(j - 1, k - 1)
def falling_to_power(A):  # sum_k A_k q^{\underline k} -> power basis (Stirling first kind)
    # q^{\underline k} = sum_j s(k,j) q^j
    @lru_cache(None)
    def s1(k, j):
        if k == 0: return 1 if j == 0 else 0
        if j == 0 or j > k: return 0
        return s1(k - 1, j - 1) - (k - 1) * s1(k - 1, j)
    poly = {}
    for k, a in enumerate(A, start=1):
        for j in range(1, k + 1): poly[j] = poly.get(j, 0) + a * s1(k, j)
    return [poly.get(j, 0) for j in range(0, max(poly) + 1)]
def padd(a, b):
    L = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(L)]
def psub(a, b): return padd(a, [-x for x in b])
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    return r
def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0: p.pop()
    return p
Nmax = max(rows)
m = [[1], [0]] + [trim(falling_to_power(rows[n])) for n in range(2, Nmax + 1)]
def powcoef(Mq, s, deg):
    res = [[1]] + [[0]] * deg
    for _ in range(s):
        new = [[0] for _ in range(deg + 1)]
        for i, a in enumerate(res):
            if any(a):
                for j, b in enumerate(Mq):
                    if i + j > deg: break
                    new[i + j] = padd(new[i + j], pmul(a, b))
        res = new
    return res
kappa = [[0]] * (Nmax + 1)
for n in range(1, Nmax + 1):
    acc = [0]
    for s in range(1, n):
        acc = padd(acc, pmul(kappa[s], powcoef(m[:n + 1], s, n - s)[n - s]))
    kappa[n] = trim(psub(m[n], acc))
for s in range(2, Nmax + 1):
    print(s, kappa[s])
