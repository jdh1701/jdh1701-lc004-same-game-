import itertools
def nc_closure(p):
    n = len(p); lab = list(p)
    changed = True
    while changed:
        changed = False
        for i, j, k, l in itertools.combinations(range(n), 4):
            if lab[i] == lab[k] and lab[j] == lab[l] and lab[i] != lab[j]:
                a, b = lab[j], lab[i]
                lab = [b if x == a else x for x in lab]; changed = True; break
    return lab
