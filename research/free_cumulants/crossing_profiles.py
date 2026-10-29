import itertools, sys
from collections import Counter
from joins import run
def crossing(x):
    n = len(x)
    return any(x[i] == x[k] and x[j] == x[l] and x[i] != x[j] for i, j, k, l in itertools.combinations(range(n), 4))
def crossed_classes(x):
    n = len(x); s = set()
    for i, j, k, l in itertools.combinations(range(n), 4):
        if x[i] == x[k] and x[j] == x[l] and x[i] != x[j]: s.add(x[i]); s.add(x[j])
    return s
for n in range(int(sys.argv[2]) if len(sys.argv) > 2 else 8, int(sys.argv[1]) + 1):
    certs, coef = run(n)
    prof = Counter(); cnt = Counter()
    for x, c in coef.items():
        if crossing(x):
            sz = Counter(x); cs = crossed_classes(x)
            key = tuple(sorted(sz[a] for a in cs))
            prof[key] += c; cnt[key] += 1
    print(f"n={n} joins_nonzero={len(coef)} crossing_nonzero={sum(cnt.values())} min_crossed_class_size="
          f"{min((min(k) for k in prof), default=None)} profile(sum c, count)={ {k:(prof[k],cnt[k]) for k in prof} }", flush=True)
