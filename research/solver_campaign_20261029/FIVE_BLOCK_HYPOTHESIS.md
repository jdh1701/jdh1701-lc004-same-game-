# Focused unconventional lead: five-block kernel

VERIFIED-COMP: the existing full signed-support tables have exactly five
NC-connected all-five-block patterns at n=10, and 35 at n=15; every such
coefficient is -1. Their cyclic orbits are respectively [5] and [5,15,15].
Script and receipt are in minimal_five_kernel.py/json. This reuses existing
exact tables; it does not rerun the expensive enumeration.

CONJECTURE, two nontrivial sizes only: for j>=2 the all-five NC-connected
nonzero support might be in bijection with noncrossing partitions of 5j points
into j blocks of size five, with coefficient -1. That familiar comparison
class has size binomial(5j,j)/(4j+1): 5,35,285,... for j=2,3,4.
Thus the next sharp prediction is [b^4]kappa_20(b)=-285, conditional on the
universal support theorem and this new unproved bijection/coefficient claim.
No novelty or statistical confidence is asserted from two matching values.
For j=1 the actual one-block coefficient at length five is -4, so the proposed
statement explicitly excludes j=1. That exception needs explanation, not hiding.

This is stronger and more falsifiable than asking whether more raw numbers
look structured. Seek a concrete transformation of five-occurrence blocks,
or a root decomposition with the five-ary-tree recurrence. A failed bijection
or a coefficient other than -1 at the next size would kill this version.
Touchard's system connectivity is not automatically the connectivity here.
