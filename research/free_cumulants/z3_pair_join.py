"""Z3: do two noncrossing 2/3-certificates ever have a join with a crossing in which one
of the crossing classes has size <= S?  Bounded evidence only (two certificates, n <= N)."""
import sys, z3, itertools

def run(n, S):
    s = z3.Solver()
    m = n // 2 + 1
    a = [[z3.Int(f"a{t}_{i}") for i in range(n)] for t in (1, 2)]
    for t in (0, 1):
        for i in range(n):
            s.add(a[t][i] >= 0, a[t][i] < m)
        for lab in range(m):
            cnt = z3.Sum([z3.If(a[t][i] == lab, 1, 0) for i in range(n)])
            s.add(z3.Or(cnt == 0, cnt == 2, cnt == 3))
        for i, j, k, l in itertools.combinations(range(n), 4):
            s.add(z3.Implies(z3.And(a[t][i] == a[t][k], a[t][j] == a[t][l]), a[t][i] == a[t][j]))
    R = [[z3.Bool(f"r0_{i}_{j}") for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            s.add(R[i][j] == z3.Or(i == j, a[0][i] == a[0][j], a[1][i] == a[1][j]))
    steps = 0
    while (1 << steps) < n:
        steps += 1
        N = [[z3.Bool(f"r{steps}_{i}_{j}") for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                s.add(N[i][j] == z3.Or([z3.And(R[i][k], R[k][j]) for k in range(n)]))
        R = N
    cross = []
    for i, j, k, l in itertools.combinations(range(n), 4):
        size_i = z3.Sum([z3.If(R[i][p], 1, 0) for p in range(n)])
        cross.append(z3.And(R[i][k], R[j][l], z3.Not(R[i][j]), size_i <= S))
    s.add(z3.Or(cross))
    return s.check()

if __name__ == "__main__":
    S = int(sys.argv[1]); out = []
    for n in range(8, int(sys.argv[2]) + 1):
        r = run(n, S); out.append(f"n={n}:{r}"); print(out[-1], flush=True)
    print("SUMMARY S<=%d " % S + " ".join(out))
