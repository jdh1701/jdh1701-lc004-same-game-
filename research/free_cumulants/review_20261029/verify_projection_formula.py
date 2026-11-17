"""
Independent verification of GPT's projection-formula identity (PR #35):
  c(A) := sum_{nonempty S subset A} (-1)^(|S|+1) * [in every coordinate i, members of S do not all agree]
should equal
  proj(A) := sum_{T subset [j]} (-1)^|T| * |pi_T(A)|
for ANY finite set A of distinct j-tuples (abstract claim, no Same-Game semantics).
This is written from scratch, not using any of GPT's or Claude's prior code.
"""
import itertools, random

def c_bruteforce(A, j):
    total = 0
    n = len(A)
    for r in range(1, n+1):
        for S in itertools.combinations(A, r):
            agrees_everywhere = True
            for i in range(j):
                vals = set(a[i] for a in S)
                if len(vals) == 1:
                    agrees_everywhere = False  # all agree on coord i -> bad, join != full
                    break
            if agrees_everywhere:
                sign = 1 if (len(S) % 2 == 1) else -1
                total += sign
    return total

def proj_formula(A, j):
    total = 0
    for mask in range(1 << j):
        T = [i for i in range(j) if (mask >> i) & 1]
        proj_set = set(tuple(a[i] for i in T) for a in A)
        sign = 1 if (len(T) % 2 == 0) else -1
        total += sign * len(proj_set)
    return total

random.seed(12345)
trials = 2000
mismatches = 0
for _ in range(trials):
    j = random.randint(1, 4)
    alphabet = random.randint(2, 4)
    size = random.randint(1, 6)
    universe = list(itertools.product(range(alphabet), repeat=j))
    random.shuffle(universe)
    A = universe[:min(size, len(universe))]
    if not A:
        continue
    lhs = c_bruteforce(A, j)
    rhs = proj_formula(A, j)
    if lhs != rhs:
        mismatches += 1
        print("MISMATCH", j, A, lhs, rhs)

print(f"trials={trials} mismatches={mismatches}")
