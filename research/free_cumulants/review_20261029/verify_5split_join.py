"""
Independent check of the lemma underlying GPT's reduction: for a 5-element set,
any two DISTINCT splits into (pair, triple) have join equal to the whole set
(the single-block partition). This is what lets "agree on coordinate i" collapse
to "same split" in the projection-formula argument.
"""
import itertools

def partition_find(parent, x):
    while parent[x] != x:
        x = parent[x]
    return x

def join_of_splits(elems, splits):
    parent = {e: e for e in elems}
    def union(a, b):
        ra, rb = partition_find(parent, a), partition_find(parent, b)
        if ra != rb: parent[ra] = rb
    for split in splits:
        for block in split:
            for a, b in itertools.combinations(block, 2):
                union(a, b)
    roots = set(partition_find(parent, e) for e in elems)
    return len(roots)

elems = [1,2,3,4,5]
splits = []
for pair in itertools.combinations(elems, 2):
    triple = tuple(e for e in elems if e not in pair)
    splits.append((pair, triple))

assert len(splits) == 10
bad = []
for s1, s2 in itertools.combinations(splits, 2):
    nblocks = join_of_splits(elems, [s1, s2])
    if nblocks != 1:
        bad.append((s1, s2, nblocks))

print(f"checked {len(list(itertools.combinations(splits,2)))} distinct pairs of splits; failures={len(bad)}")
if bad:
    print(bad)
