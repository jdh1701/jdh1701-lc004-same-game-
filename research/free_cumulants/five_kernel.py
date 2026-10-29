"""All-five connected kernel: coefficient c(x) for x with every class of size 5 and NC-connected.
c(x) = crosscut sum over certificates below x, computed by the signed-join recursion restricted to atoms below x."""
import sys, itertools
from collections import Counter
from joins import canon, join
from nc_factorization_check_lib import nc_closure

def set_partitions_blocksize(n, size):
    """canonical RGS labellings with all classes of exactly `size` points"""
    j = n // size
    lab = [None] * n
    def rec(i, used, counts):
        if i == n:
            yield tuple(lab); return
        for c in range(min(used + 1, j)):
            if counts[c] < size:
                lab[i] = c; counts[c] += 1
                yield from rec(i + 1, max(used, c + 1), counts)
                counts[c] -= 1
    yield from rec(0, 0, [0] * j)

def noncrossing_labels(lab):
    n = len(lab)
    return not any(lab[i] == lab[k] and lab[j] == lab[l] and lab[i] != lab[j]
                   for i, j, k, l in itertools.combinations(range(n), 4))

def atoms_below(x):
    """certificates (all classes 2/3, NC) refining x: split each 5-class into a pair and a triple."""
    n = len(x); classes = {}
    for i, c in enumerate(x): classes.setdefault(c, []).append(i)
    choices = []
    for pos in classes.values():
        opts = []
        for pr in itertools.combinations(pos, 2):
            tr = tuple(p for p in pos if p not in pr)
            opts.append((pr, tr))
        choices.append(opts)
    out = []
    for combo in itertools.product(*choices):
        lab = [None] * n; m = 0
        for pr, tr in combo:
            for blk in (pr, tr):
                for p in blk: lab[p] = m
                m += 1
        if noncrossing_labels(lab): out.append(canon(lab))
    return out

def coefficient(x):
    atoms = atoms_below(x)
    coef = {}
    for g in atoms:
        new = dict(coef)
        for y, c in coef.items():
            z = join(y, g); new[z] = new.get(z, 0) - c
        new[g] = new.get(g, 0) + 1
        coef = {k: v for k, v in new.items() if v}
    return coef.get(canon(list(x)), 0), len(atoms)

if __name__ == "__main__":
    n = int(sys.argv[1]); dist = Counter(); found = []
    cand = 0
    for x in set_partitions_blocksize(n, 5):
        if len(set(nc_closure(list(x)))) != 1: continue
        cand += 1
        c, na = coefficient(x)
        dist[c] += 1
        if c: found.append((x, c))
    print(f"n={n}: connected all-five candidates={cand}; coefficient distribution={dict(dist)}")
    for x, c in found[:12]: print(c, "".join(map(str, x)) if max(x) < 10 else x)
