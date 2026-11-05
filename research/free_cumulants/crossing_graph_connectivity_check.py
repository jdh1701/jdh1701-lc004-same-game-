"""Correctly-scoped check (small n, fast): for every NC-connected set
partition p of [n] with >= 2 blocks, is EVERY block crossed by at least
one single other block (a literal witness a<b<c<d with a,c in one block,
b,d in another, a,b in different blocks)?

This is the exact gap flagged in WORKBOARD.md 2026-10-30 04:32: my proved
Lean theorem winningJoinCoefficient_ne_zero_crossed_class_card_ge_five only
fires on classes that are literally crossed by a single other class. To
turn it into "at the n=5j boundary every class has size exactly 5" I need
"NCConnected with >=2 classes implies every class is crossed by some
single other class" -- NOT yet established, possibly false as I suspect
from the naive 2-block-merge counterexample attempt.

Definitions match the Lean development exactly:
- PatternNoncrossing q: no a<b<c<d with q(a,c), q(b,d), not q(a,b).
- NCConnected p: no coarsening q >= p, q noncrossing, q != top (single block).
  (ncConnected_iff_no_proper_noncrossing_coarsening)
- "block X crossed by block Y": exists a<b<c<d with a,c in X, b,d in Y
  (or a,c in Y, b,d in X), a and b in different blocks (automatic since
  X != Y).

Brute force over ALL set partitions of [n], n = 4..9.
"""
import itertools
from functools import lru_cache

def partitions(s):
    s = list(s)
    if not s:
        yield []
        return
    if len(s) == 1:
        yield [frozenset(s)]
        return
    first, rest = s[0], s[1:]
    for smaller in partitions(rest):
        for i in range(len(smaller)):
            yield smaller[:i] + [smaller[i] | {first}] + smaller[i+1:]
        yield [frozenset({first})] + smaller

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

def refines(p_blocks, q_blocks):
    # p refines q: every block of p is a subset of some block of q
    qmap = {}
    for b in q_blocks:
        for x in b:
            qmap[x] = b
    for b in p_blocks:
        target = qmap[next(iter(b))]
        if not b <= target:
            return False
    return True

def is_nc_connected(p_blocks, n):
    # Only need to consider coarsenings formed by merging p's OWN blocks
    # together (any coarsening of p is a union of groups of p's blocks),
    # so enumerate partitions of the block-index set, not of all n points.
    k = len(p_blocks)
    if k <= 1:
        return True
    blocks_list = list(p_blocks)
    for grouping in partitions(list(range(k))):
        if len(grouping) == 1:
            continue  # that's the trivial top coarsening
        q_blocks = [frozenset().union(*(blocks_list[i] for i in group)) for group in grouping]
        if is_noncrossing(q_blocks):
            return False  # proper noncrossing coarsening exists -> NOT connected
    return True

def crossed_by_single_other(p_blocks):
    """For each block X, is there a single other block Y and a<b<c<d with
    a,c in X, b,d in Y (or a,c in Y, b,d in X)?"""
    results = {}
    for X in p_blocks:
        found = False
        for Y in p_blocks:
            if Y == X:
                continue
            pts = sorted(X | Y)
            for a, b_, c, d in itertools.combinations(pts, 4):
                sides = [a in X, b_ in X, c in X, d in X]
                # want a,c same block, b,d same block (the other), a!=b block
                if sides[0] == sides[2] and sides[1] == sides[3] and sides[0] != sides[1]:
                    found = True
                    break
            if found:
                break
        results[X] = found
    return results

def main():
    for n in range(4, 10):
        print(f"=== n={n} ===", flush=True)
        total_connected_multi = 0
        counterexamples = []
        for blocks in partitions(list(range(n))):
            if len(blocks) < 2:
                continue
            if not is_nc_connected(blocks, n):
                continue
            total_connected_multi += 1
            cr = crossed_by_single_other(blocks)
            if not all(cr.values()):
                counterexamples.append((blocks, cr))
        print(f"  NC-connected multi-block partitions: {total_connected_multi}")
        print(f"  counterexamples (some block NOT crossed by a single other): {len(counterexamples)}")
        for blocks, cr in counterexamples[:5]:
            uncrossed = [sorted(X) for X, ok in cr.items() if not ok]
            print(f"    example blocks={[sorted(b) for b in blocks]} uncrossed_blocks={uncrossed}")
        if counterexamples:
            print(f"  LEMMA FALSE at n={n}")
        else:
            print(f"  lemma holds for all NC-connected multi-block partitions at n={n}")

if __name__ == "__main__":
    main()
