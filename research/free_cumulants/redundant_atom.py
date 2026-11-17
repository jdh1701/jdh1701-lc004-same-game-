"""For crossing joins x with a crossed class of size 4: is there a certificate a <= x that lies in no
irredundant generating set of x?  Then F <-> F xor {a} is a sign-reversing involution and c(x)=0."""
import itertools, sys
from collections import Counter
from joins import run, gen, rgs_of_blocks, join
from crossing_profiles import crossing, crossed_classes
def below_of(x, certs): return [c for c in certs if join(c, x) == x]
def analyse(n, limit=16):
    certs = sorted({rgs_of_blocks(n, c) for c in gen(0, n)})
    seen = set(); res = Counter(); skipped = 0
    # candidate x: all joins of pairs/triples-subsets reachable; take from coefficient support plus zero ones
    cand = set()
    for a in certs:
        for b in certs:
            y = join(a, b)
            if crossing(y): cand.add(y)
    for x in cand:
        sz = Counter(x)
        if not any(sz[c] == 4 for c in crossed_classes(x)): continue
        B = below_of(x, certs)
        if len(B) > limit: skipped += 1; continue
        # sup of every subset via bitmask
        m = len(B); sup = {0: None}
        irredundant_members = set()
        gens = []
        for mask in range(1, 1 << m):
            low = mask & -mask; i = low.bit_length() - 1
            prev = sup[mask ^ low]
            sup[mask] = B[i] if prev is None else join(prev, B[i])
        gens = [mk for mk in range(1, 1 << m) if sup[mk] == x]
        gset = set(gens)
        # a is in some irredundant generating set iff exists mask in gens containing a with no proper sub-mask-removal of a... check minimal sets
        minimal_used = set()
        for mk in gens:
            if all((mk & ~(1 << i)) not in gset for i in range(m) if mk >> i & 1):
                for i in range(m):
                    if mk >> i & 1: minimal_used.add(i)
        red = [i for i in range(m) if i not in minimal_used]
        # sign-reversing involution works if some a is never needed: removal keeps sup for every generating F containing a
        ok = any(all(((mk & ~(1 << i)) in gset) for mk in gens if mk >> i & 1) for i in range(m))
        tot = sum((-1) ** (bin(mk).count("1") + 1) for mk in gens)
        res[(ok, tot == 0)] += 1
    return res, skipped, len(cand)
if __name__ == "__main__":
    for n in range(8, int(sys.argv[1]) + 1):
        print(n, analyse(n), flush=True)
