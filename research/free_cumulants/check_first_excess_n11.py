"""Exhaustively check PR43's first-excess claim (coefficient == -1 for every
NCConnected (5,6)-profile pattern at n=5j+1, j=2 i.e. n=11) using the
project's existing certificate-join coefficient calculator.

Two bugs fixed during development, both left documented here on purpose:
(1) an earlier version omitted the NCConnected filter entirely, which
    produced 11 spurious "coefficient=4" (5,6)-profile hits -- these turned
    out to be simple two-interval (already-noncrossing, hence NOT
    NCConnected) patterns, not real counterexamples;
(2) a later version computed `profile = sorted(Counter(sizes).values())`
    (sizes of each distinct size-VALUE's multiplicity) instead of
    `sorted(len(b) for b in blocks)` (the actual block sizes) -- this
    silently produced a bogus profile=(1,1) bucket. Fixed below."""
import sys, itertools
sys.path.insert(0, "..")
from certificate_join_count import join_coefficients
from collections import Counter

def tuple_to_blocks(pat):
    d = {}
    for i, lab in enumerate(pat):
        d.setdefault(lab, set()).add(i)
    return list(d.values())

def is_noncrossing(blocks):
    pos_block = {}
    for b in blocks:
        for x in b:
            pos_block[x] = tuple(sorted(b))
    pts = sorted(pos_block)
    for a, b_, c, d in itertools.combinations(pts, 4):
        if pos_block[a] == pos_block[c] and pos_block[b_] == pos_block[d] and pos_block[a] != pos_block[b_]:
            return False
    return True

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

def is_nc_connected(blocks):
    k = len(blocks)
    if k <= 1:
        return True
    blocks_list = [frozenset(b) for b in blocks]
    for grouping in partitions_of_indices(list(range(k))):
        if len(grouping) == 1:
            continue
        q_blocks = [frozenset().union(*(blocks_list[i] for i in group)) for group in grouping]
        if is_noncrossing(q_blocks):
            return False
    return True

n = 11
weights, certs = join_coefficients(n)

profile_coeffs = {}
bad = []
checked_56 = 0
for pat, coeff in weights.items():
    assert len(pat) == n
    blocks = tuple_to_blocks(pat)
    k = len(blocks)
    if k < 2:
        continue
    if not is_nc_connected(blocks):
        continue
    profile = tuple(sorted(len(b) for b in blocks))
    profile_coeffs.setdefault(profile, Counter())[coeff] += 1
    if profile == (5, 6):
        checked_56 += 1
        if coeff != -1:
            bad.append((pat, coeff))

print(f"n={n}; NCConnected multi-class nonzero-coefficient patterns by profile:")
for profile, counts in sorted(profile_coeffs.items()):
    print(f"  profile={profile}: coeff dist={dict(counts)}")

print(f"\n(5,6)-profile NCConnected patterns checked: {checked_56}")
print(f"  with coefficient != -1: {len(bad)}")
for pat, coeff in bad[:10]:
    print("   COUNTEREXAMPLE", pat, coeff)
if not bad:
    print("  CONFIRMED: every NCConnected (5,6)-profile nonzero pattern at n=11 (j=2) has coefficient exactly -1.")
