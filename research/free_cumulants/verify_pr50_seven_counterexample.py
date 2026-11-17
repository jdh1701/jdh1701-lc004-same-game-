"""Independently verify PR50's claimed explicit (5,5,7) nonzero counterexample:
pattern = 0 2 2 0 1 1 2 2 1 2 2 1 1 0 0 2 0  (n=17), claimed
winningJoinCoefficient = +1.

Rather than enumerate ALL noncrossing certificates of n=17 (infeasible --
the project's own certificate_join_count.py scales ~7x per unit of n and
is already too slow past n=13), restrict directly to the mathematical
definition: winningJoinCoefficient(p) only depends on certificates c with
CertificateConstraint c (noncrossing, blocks of size 2 or 3) AND c <= p
(every block of c lies within a single class of p). For this specific p
with class sizes (5,5,7), the only size-decompositions into parts of
{2,3} are 5=2+3 (unique shape) and 7=2+2+3 (unique shape), so the set of
candidate certificates refining p is small and enumerable directly.
"""
import itertools
from collections import defaultdict

pattern = [0,2,2,0,1,1,2,2,1,2,2,1,1,0,0,2,0]
n = len(pattern)
assert n == 17

classes = defaultdict(list)
for i, lab in enumerate(pattern):
    classes[lab].append(i)
sizes = {lab: len(pts) for lab, pts in classes.items()}
print("class sizes:", sizes)

def block_decompositions(points):
    """All ways to partition `points` into blocks of size 2 or 3 (as a set
    of frozensets), covering every point exactly once."""
    points = list(points)
    k = len(points)
    results = []
    def rec(remaining, blocks):
        if not remaining:
            results.append(tuple(blocks))
            return
        first = remaining[0]
        rest = remaining[1:]
        # pair
        for partner in rest:
            r2 = [x for x in rest if x != partner]
            rec(r2, blocks + [frozenset({first, partner})])
        # triple
        for p2, p3 in itertools.combinations(rest, 2):
            r3 = [x for x in rest if x != p2 and x != p3]
            rec(r3, blocks + [frozenset({first, p2, p3})])
    rec(points, [])
    return results

per_class_decomps = {lab: block_decompositions(pts) for lab, pts in classes.items()}
for lab, decs in per_class_decomps.items():
    print(f"  class {lab} (size {sizes[lab]}): {len(decs)} block-decompositions")

def is_noncrossing(blocks):
    pos_block = {}
    for b in blocks:
        for x in b:
            pos_block[x] = b
    pts = sorted(pos_block)
    for a, b_, c, d in itertools.combinations(pts, 4):
        if pos_block[a] == pos_block[c] and pos_block[b_] == pos_block[d] and pos_block[a] != pos_block[b_]:
            return False
    return True

def canonical(blocks, n):
    labels = [None]*n
    for j, b in enumerate(sorted(tuple(sorted(x)) for x in blocks)):
        for i in b:
            labels[i] = j
    return tuple(labels)

labs = sorted(per_class_decomps)
candidates = []
total_raw = 1
for lab in labs:
    total_raw *= len(per_class_decomps[lab])
print("raw combinations before noncrossing filter:", total_raw)

for combo in itertools.product(*(per_class_decomps[lab] for lab in labs)):
    all_blocks = [b for decs in combo for b in decs]
    if is_noncrossing(all_blocks):
        candidates.append(canonical(all_blocks, n))

candidates = list(set(candidates))
print("noncrossing certificates refining p:", len(candidates))

def join(p, q):
    parent = list(range(len(p)))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for w in (p, q):
        first = {}
        for i, a in enumerate(w):
            if a in first:
                parent[root(i)] = root(first[a])
            else:
                first[a] = i
    names = {}
    return tuple(names.setdefault(root(i), len(names)) for i in range(len(p)))

p_canon = canonical([frozenset(pts) for pts in classes.values()], n)

# Mobius-style incremental build (same recurrence as certificate_join_count.py's
# join_coefficients, but only over the certificates that actually refine p).
weights = {}
for c in candidates:
    delta = defaultdict(int)
    delta[c] += 1
    for pat, a in weights.items():
        delta[join(pat, c)] -= a
    for pat, a in delta.items():
        weights[pat] = weights.get(pat, 0) + a
        if not weights[pat]:
            del weights[pat]

coeff = weights.get(p_canon, 0)
print()
print("winningJoinCoefficient(p) computed independently:", coeff)
print("PR50 claims coefficient = +1 ->", "CONFIRMED" if coeff == 1 else "MISMATCH")

# Also independently confirm NCConnected (class-crossing graph connected / no
# proper noncrossing coarsening), since PR50 also claims this.
def partitions_of_indices(idxs):
    idxs = list(idxs)
    if not idxs:
        yield []
        return
    if len(idxs) == 1:
        yield [frozenset(idxs)]
        return
    first, rest = idxs[0], idxs[1:]
    for smaller in partitions_of_indices(rest):
        for i in range(len(smaller)):
            yield smaller[:i] + [smaller[i] | {first}] + smaller[i+1:]
        yield [frozenset({first})] + smaller

blocks_list = [frozenset(pts) for pts in classes.values()]
k = len(blocks_list)
connected = True
for grouping in partitions_of_indices(list(range(k))):
    if len(grouping) == 1:
        continue
    q_blocks = [frozenset().union(*(blocks_list[i] for i in group)) for group in grouping]
    if is_noncrossing(q_blocks):
        connected = False
        break
print("NCConnected (no proper noncrossing coarsening) independently checked:", connected)
