"""Exact counting of winning Same Game colour patterns by excess j = n - 2k.

A winning pattern = special classes (size >= 3) on r positions + a perfect
matching M of 2-classes on the remaining positions, such that some
noncrossing refinement Q of the special classes into blocks of size 2/3
makes Q u M noncrossing (Biedl et al. / LC004 certificate theorem).

For a fixed special structure S (partition of r cyclic points) the set of
valid M is a union over refinements Q of X_Q = {M NC, M separates no block
of Q}.  Intersections are X_{ncclosure(join)}.  |X_Pi| is a sum over gap
sizes of a product over faces of Pi of Catalan numbers.
"""
import sys
from functools import lru_cache
from itertools import combinations
from math import comb
from fractions import Fraction

def catalan(m): return comb(2*m, m)//(m+1)

def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]

def crosses(A, B):
    for a1, a2 in combinations(sorted(A), 2):
        for b in B:
            pass
    # A and B cross iff exist a1<b1<a2<b2 or b1<a1<b2<a2
    for a1, a2 in combinations(sorted(A), 2):
        inside = any(a1 < b < a2 for b in B)
        outside = any(b < a1 or b > a2 for b in B)
        if inside and outside:
            return True
    return False

def is_nc(blocks):
    for i in range(len(blocks)):
        for j in range(i+1, len(blocks)):
            if crosses(blocks[i], blocks[j]):
                return False
    return True

def nc_refinements(S):
    """All NC partitions refining S with block sizes in {2,3}."""
    per_class = []
    for cls in S:
        opts = [p for p in set_partitions(sorted(cls))
                if all(len(b) in (2, 3) for b in p) and is_nc(p)]
        per_class.append(opts)
    res = []
    def rec(i, acc):
        if i == len(per_class):
            if is_nc(acc):
                res.append(frozenset(frozenset(b) for b in acc))
            return
        for o in per_class[i]:
            rec(i+1, acc + o)
    rec(0, [])
    return res

def nc_closure(blocks, r):
    """Smallest NC partition coarser than given blocks (merge crossing)."""
    parent = list(range(r))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for b in blocks:
        b = list(b)
        for x in b[1:]:
            parent[find(x)] = find(b[0])
    changed = True
    while changed:
        changed = False
        groups = {}
        for x in range(r):
            groups.setdefault(find(x), []).append(x)
        gl = list(groups.values())
        for i in range(len(gl)):
            for j in range(i+1, len(gl)):
                if crosses(gl[i], gl[j]):
                    parent[find(gl[i][0])] = find(gl[j][0])
                    changed = True
                    break
            if changed:
                break
    groups = {}
    for x in range(r):
        groups.setdefault(find(x), []).append(x)
    return frozenset(frozenset(g) for g in groups.values())

def faces(Pi, r):
    """Gaps g=0..r-1 (gap g after point g, gap r-1 is the outer one).
    Return list of (number_of_circular_gaps, contains_outer)."""
    parent = list(range(r))
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for g1 in range(r):
        for g2 in range(g1+1, r):
            # points strictly between gap g1 and gap g2: g1+1..g2
            seg = set(range(g1+1, g2+1))
            if not any((B & seg) and (B - seg) for B in Pi):
                parent[find(g2)] = find(g1)
    groups = {}
    for g in range(r):
        groups.setdefault(find(g), []).append(g)
    return [(len(v), (r-1) in v) for v in groups.values()]

def face_series(d, outer, Nmax):
    """sum over N of (#ways to place 2N free points into the face's linear gaps) * Cat(N)."""
    parts = d + (1 if outer else 0)
    return [comb(2*N + parts - 1, parts - 1) * catalan(N) for N in range(Nmax+1)]

def polymul(a, b, Nmax):
    c = [0]*(Nmax+1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b[:Nmax+1-i]):
            c[i+j] += x*y
    return c

@lru_cache(None)
def X_series(Pi, r, Nmax):
    s = [1] + [0]*Nmax
    for d, outer in faces(Pi, r):
        s = polymul(s, face_series(d, outer, Nmax), Nmax)
    return tuple(s)

def union_series(refs, r, Nmax):
    """|union_Q X_Q| as series in N via inclusion-exclusion, grouping by closure."""
    total = [0]*(Nmax+1)
    m = len(refs)
    # inclusion-exclusion over subsets (m is small)
    from itertools import combinations as C
    for t in range(1, m+1):
        sign = 1 if t % 2 else -1
        for T in C(range(m), t):
            blocks = [b for i in T for b in refs[i]]
            Pi = nc_closure(blocks, r)
            xs = X_series(Pi, r, Nmax)
            for N in range(Nmax+1):
                total[N] += sign * xs[N]
    return total

def profiles(j):
    """Multisets of class sizes >=3 with sum(s-2) = j."""
    out = []
    def rec(rem, maxs, acc):
        if rem == 0:
            out.append(tuple(acc)); return
        for s in range(min(maxs, rem+2), 2, -1):
            rec(rem-(s-2), s, acc+[s])
    rec(j, j+2, [])
    return out

def special_structures(sizes):
    """All set partitions of range(r) with the given multiset of block sizes."""
    r = sum(sizes)
    target = sorted(sizes)
    for p in set_partitions(list(range(r))):
        if sorted(len(b) for b in p) == target:
            yield [frozenset(b) for b in p]

def diagonal(j, Nmax):
    """D_j[N] = number of winning patterns with excess j and N pair-classes.
    k = c + N where c = number of special classes; n = 2k + j."""
    by_k = {}
    for sizes in profiles(j):
        c = len(sizes); r = sum(sizes)
        acc = [0]*(Nmax+1)
        for S in special_structures(sizes):
            refs = nc_refinements(S)
            if not refs: continue
            u = union_series(refs, r, Nmax)
            for N in range(Nmax+1): acc[N] += u[N]
        for N in range(Nmax+1):
            by_k[c+N] = by_k.get(c+N, 0) + acc[N]
    return by_k

if __name__ == "__main__":
    j = int(sys.argv[1]); Nmax = int(sys.argv[2])
    d = diagonal(j, Nmax)
    for k in sorted(d):
        if k <= Nmax: print(k, 2*k+j, d[k])

def nc23(points):
    """NC partitions of sorted list `points` into blocks of size 2/3."""
    if not points:
        yield []
        return
    a = points[0]; rest = points[1:]; L = len(rest)
    for i in range(L):
        # block {a, rest[i]} : inside rest[:i], outside rest[i+1:]
        for left in nc23(rest[:i]):
            for right in nc23(rest[i+1:]):
                yield [(a, rest[i])] + left + right
        for j2 in range(i+1, L):
            for p1 in nc23(rest[:i]):
                for p2 in nc23(rest[i+1:j2]):
                    for p3 in nc23(rest[j2+1:]):
                        yield [(a, rest[i], rest[j2])] + p1 + p2 + p3

def special_structures_fast(j):
    """All special structures S (classes of size>=3, excess j) having an NC 2/3 refinement.
    Returns dict r -> set of S (frozenset of frozensets)."""
    out = {}
    # r ranges: each class size s contributes s-2 to j and has s>=3 => r = j + 2c, c<=j
    for c in range(1, j+1):
        r = j + 2*c
        found = set()
        for Q in nc23(list(range(r))):
            b = len(Q)
            for grp in set_partitions(list(range(b))):
                if len(grp) != c: continue
                cls = [frozenset(x for bi in g for x in Q[bi]) for g in grp]
                if all(len(x) >= 3 for x in cls):
                    found.add(frozenset(cls))
        out[r] = found
    return out

def diagonal_fast(j, Nmax):
    by_k = {}
    ss = special_structures_fast(j)
    for r, structs in ss.items():
        c = (r - j)//2
        acc = [0]*(Nmax+1)
        for S in structs:
            refs = nc_refinements([sorted(x) for x in S])
            u = union_series(refs, r, Nmax)
            for N in range(Nmax+1): acc[N] += u[N]
        for N in range(Nmax+1):
            by_k[c+N] = by_k.get(c+N, 0) + acc[N]
        print(f"  r={r} structures={len(structs)}", file=sys.stderr)
    return by_k

def upset(refs, r):
    """All NC partitions of [r] coarser than some member of refs."""
    start = {nc_closure(list(q), r) for q in refs}
    seen = set(start); stack = list(start)
    while stack:
        P = stack.pop()
        bl = list(P)
        for i in range(len(bl)):
            for j2 in range(i+1, len(bl)):
                Q = nc_closure([b for t, b in enumerate(bl) if t not in (i, j2)] + [bl[i] | bl[j2]], r)
                if Q not in seen:
                    seen.add(Q); stack.append(Q)
    return seen

def leq(Z, P):
    """Z finer than or equal to P."""
    return all(any(b <= B for B in P) for b in Z)

def union_series_mobius(refs, r, Nmax):
    U = sorted(upset(refs, r), key=len)  # coarser (fewer blocks) first
    E = {}
    total = [0]*(Nmax+1)
    for Z in U:
        xs = list(X_series(Z, r, Nmax))
        for P in E:
            if P != Z and len(P) < len(Z) and leq(Z, P):
                e = E[P]
                for N in range(Nmax+1): xs[N] -= e[N]
        E[Z] = xs
        for N in range(Nmax+1): total[N] += xs[N]
    return total

def diagonal_mobius(j, Nmax):
    by_k = {}
    ss = special_structures_fast(j)
    for r, structs in ss.items():
        c = (r - j)//2
        acc = [0]*(Nmax+1)
        for S in structs:
            refs = nc_refinements([sorted(x) for x in S])
            u = union_series_mobius(refs, r, Nmax)
            for N in range(Nmax+1): acc[N] += u[N]
        for N in range(Nmax+1):
            by_k[c+N] = by_k.get(c+N, 0) + acc[N]
        print(f"  r={r} structures={len(structs)}", file=sys.stderr, flush=True)
    return by_k
