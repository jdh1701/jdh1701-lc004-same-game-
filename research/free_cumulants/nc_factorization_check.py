"""Independent check of GPT's winningJoinCoefficient_noncrossing_product:
c_n(p) = prod over blocks B of nc(p) of c_|B|(p restricted to B), for ALL set partitions p of [n], n<=N.
c comes from joins.py (signed certificate-join sums), computed independently of GPT's code."""
import sys, itertools
from joins import run, canon
N = int(sys.argv[1])
C = {0: {(): 1}, 1: {(0,): 0}}   # c_0 = 1 (empty), c_1: single point is not winning -> 0
for m in range(2, N + 1):
    C[m] = run(m)[1]
def set_partitions(n):
    def rec(i, lab, m):
        if i == n: yield tuple(lab); return
        for c in range(m + 1):
            lab.append(c); yield from rec(i + 1, lab, max(m, c + 1) if c == m else m); lab.pop()
    yield from rec(0, [], 0)
def nc_closure(p):
    n = len(p); lab = list(p)
    changed = True
    while changed:
        changed = False
        for i, j, k, l in itertools.combinations(range(n), 4):
            if lab[i] == lab[k] and lab[j] == lab[l] and lab[i] != lab[j]:
                a, b = lab[j], lab[i]
                lab = [b if x == a else x for x in lab]; changed = True; break
    return lab
bad = 0; tested = 0; nonzero = 0
for n in range(2, N + 1):
    for p in set_partitions(n):
        lab = nc_closure(p)
        prod = 1
        for blk in set(lab):
            pos = [i for i in range(n) if lab[i] == blk]
            sub = canon([p[i] for i in pos])
            prod *= C[len(pos)].get(sub, 0) if len(pos) >= 2 else 0
            if prod == 0: break
        direct = C[n].get(canon(list(p)), 0)
        tested += 1; nonzero += direct != 0
        if prod != direct:
            bad += 1
            if bad <= 5: print("MISMATCH", p, "direct", direct, "product", prod)
    print(f"n={n}: cumulative tested={tested} nonzero={nonzero} mismatches={bad}", flush=True)
print("RESULT", "FACTORIZATION HOLDS on all tested partitions" if bad == 0 else "FACTORIZATION FAILS")
