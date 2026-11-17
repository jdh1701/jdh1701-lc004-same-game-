import sys, itertools
from collections import Counter
def load(paths):
    pats = set()
    for p in paths:
        for l in open(p):
            l = l.strip()
            if l and l.isalpha() and l.islower(): pats.add(l)
    return sorted(pats)
def canon(w):
    d = {}; return tuple(d.setdefault(a, len(d)) for a in w)
def crossing(w, a, b):
    seq = [c for c in w if c in (a, b)]
    pat = [seq[0], b if seq[0] == a else a] * 2; k = 0
    for c in seq:
        if c == pat[k]:
            k += 1
            if k == 4: return True
    return False
def analyse(pats, n):
    P = {canon(p) for p in pats}
    orb = Counter(); seen = set(); refl = 0
    for w in P:
        if w in seen: continue
        o = {canon(w[i:] + w[:i]) for i in range(n)}; seen |= o
        orb[len(o)] += 1
    reflsym = sum(1 for w in P if canon(w[::-1]) == w)
    g = Counter(); edges = Counter()
    for w in P:
        cl = sorted(set(w)); E = [(a, b) for a, b in itertools.combinations(cl, 2) if crossing(w, a, b)]
        deg = tuple(sorted(sum(1 for e in E if c in e) for c in cl))
        g[(len(E), deg)] += 1
    # cyclic gap structure of each class
    gaps = Counter()
    for w in P:
        for c in set(w):
            pos = [i for i, x in enumerate(w) if x == c]
            gp = tuple(sorted(((pos[(k + 1) % 5] - pos[k]) % n) for k in range(5)))
            gaps[gp] += 1
    return len(P), dict(orb), reflsym, dict(g), gaps.most_common(8)
if __name__ == "__main__":
    n = int(sys.argv[1]); pats = load(sys.argv[2:])
    cnt, orb, rs, g, gaps = analyse(pats, n)
    print(f"n={n}: patterns={cnt} orbit sizes (rotation)={orb} reflection-symmetric={rs}")
    print("  crossing graph (edges, degree sequence): count =", g)
    print("  most common sorted cyclic gap multisets per class:", gaps)
