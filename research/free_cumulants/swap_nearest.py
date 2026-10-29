import itertools, sys
from five_kernel import set_partitions_blocksize, noncrossing_labels
def dist(x, y, j):
    best = None
    for perm in itertools.permutations(range(j)):
        d = sum(1 for a, b in zip(x, y) if perm[b] != a)
        if best is None or d < best: best = d
    return best
n = int(sys.argv[1]); j = n // 5
NC = [y for y in set_partitions_blocksize(n, 5) if noncrossing_labels(y)]
print("NC all-five partitions:", len(NC))
pats = [tuple(int(c) for c in s) for s in sys.argv[2:]]
for x in pats:
    ds = sorted((dist(x, y, j), "".join(map(str, y))) for y in NC)
    print("".join(map(str, x)), "nearest NC:", ds[:3])
