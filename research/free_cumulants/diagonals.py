from math import comb
from fractions import Fraction as F
rows = {}
for l in open("rows.txt"):
    n, v = l.split(":"); rows[int(n)] = [int(x) for x in v.split()]
P = {1: lambda k: F(1), 2: lambda k: F(k), 3: lambda k: F((2*k-1)*(k+2), 3),
     4: lambda k: F(5*k**3 + 17*k**2 - 5*k - 5, 12),
     5: lambda k: F(13*k**4 + 85*k**3 + 75*k**2 - 155*k + 42, 60)}
checks = 0
for j, f in P.items():
    for k in range(1, 9):
        n = 2*k + j
        if n in rows and k - 1 < len(rows[n]) and n >= 2:
            assert rows[n][k-1] == f(k) * comb(n, k-1), (j, k)
            checks += 1
print("A(2k+j,k) = C(2k+j,k-1)*P_j(k) verified at", checks, "data points; j<=5")
print("PREDICTION A(16,6) =", f(6) * comb(16, 5))

extra = {(16, 6): 603148, (15, 6): 88088, (16, 7): 56056, (17, 6): 3817996, (17, 8): 19448}  # bf-k run 40844840701
for (n, k), v in extra.items():
    j = n - 2*k
    assert v == P[j](k) * comb(n, k-1), (n, k)
print("bf-k sharded brute-force entries match: A(16,6)=603148 (the prediction), A(15,6), A(16,7)")
