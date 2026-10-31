# Adjacent inflation: an exact local rule and a sign obstruction

2026-10-31. The all-length Same Game enumeration remains OPEN.
Base: PR44 receipt c98dc7bfb5b4f12f5b2f1d1d4283f9bd3b23be12. A repository
recheck found no intervening proof changes in PR35 or PR41–44.

## New unbounded paper theorem

Let p partition cyclically ordered positions into j>=2 five-point classes.
Suppose its COMPLETE original noncrossing 2/3 certificate family is exactly
{a,b}, and a join b = p. Choose two consecutive positions in the same class,
and insert one further occurrence between them, obtaining p+.

Then the complete certificate family of p+ has either three or four elements,
and its original coefficient is determined exactly as follows:

| The designated adjacent pair in the source | Generators after inflation | Coefficient of p+ |
|---|---:|---:|
| A two-point block of a or b | 3 | -1 |
| A two-point block of neither | 4 | +1 |

The original coefficient of p is -1 by the existing two-generator theorem.
Thus preservation of coefficient -1 is EQUIVALENT to the designated adjacent
pair being a block in one source certificate. It cannot be a block in both,
since that would give the same local five-point partition in both generators,
contradicting their full join.

Status: PROVED-PAPER, conditional on the stated complete-family/full-join
hypotheses. The local gap identities, unbounded context/family transfer,
regular-state exclusion, local lift count, and generic positive coefficient
lemma are formalized separately; see receipts.json for their compilation status.
The full original-position gap encoding and assembly of this paper theorem
are NOT claimed as a completed Lean theorem.

No actual +1 connected first-excess game pattern is exhibited. The second
branch may be geometrically impossible for these source families. Ruling it
out is now a concrete, falsifiable remaining theorem; it must not be assumed.

## Proof from original positions

Rotate so that the chosen adjacent old occurrences are class ranks 0 and 1
at the beginning of the linear order. All positions of other classes lie in
four gaps: after old rank1, after rank2, after rank3, or after rank4. The gap
between ranks0 and1 is empty. After insertion the first three class positions
are consecutive, and the same four outside gaps remain in the same order.
Within each outside gap, the order of outside positions is unchanged.

For crossing tests only, represent the old class points by 0,2,4,6,8 and
outside gaps by 3,5,7,9. Represent the new points by 0,2,4,6,8,10 and gaps by
5,7,9,11. For an outside certificate block B, test every pair of its endpoints
against every same-block pair of the distinguished local certificate. If the
outside endpoints occupy one gap, neither configuration can cross. If they
occupy different gaps, their relative order to every class point is exactly
the representative order. Thus these finite chord tests are equivalent to
actual block noncrossing, for arbitrarily many original positions.

Here is the complete catalogue in the existing Lean order. Vertical bars
separate blocks; digits are class ranks, not original position numbers.

| Old state | Five-point certificate |
|---:|---|
| 0 | 012 / 34 |
| 1 | 014 / 23 |
| 2 | 01 / 234 |
| 3 | 034 / 12 |
| 4 | 04 / 123 |

| New state | Six-point certificate | Same outside compatibility as old state |
|---:|---|---:|
| 0 | 012 / 345 | 2 |
| 1 | 015 / 234 | 4 |
| 2 | 01 / 23 / 45 | 0 |
| 3 | 01 / 25 / 34 | 1 |
| 4 | 03 / 12 / 45 | 0 |
| 5 | 045 / 123 | 3 |
| 6 | 05 / 12 / 34 | 1 |
| 7 | 05 / 14 / 23 | 4 |

Each row is an exact equality of all sixteen ordered outside-gap pair tests.
The same calculation also shows: if old state3 or4 is compatible with an
outside block, ALL five old states are compatible with that block. Therefore,
if either occurs with a complete outside configuration, the original pattern
has at least five certificates. Under the two-certificate hypothesis they are
excluded. This uses the complete family, not just two selected certificates.

Fix a configuration x of certificates on every other class. Their own internal
and mutual compatibility is unchanged by insertion. The table shows that the
new complete configurations over x are precisely the inverse image of the
old feasible local states under [2,4,0,1,0,3,1,4]. There are no additional new
certificates, and all listed inverse images really are certificates. The
original complete family therefore lifts without omitted or duplicated tuples.
This is the unbounded context transfer represented by the Lean definitions.

Because a join b = p, their local restrictions differ in EVERY class. Their
outside configurations are therefore distinct (j>=2), and their distinguished
states form one of {0,2}, {1,2}, or {0,1}. State2 is exactly the designated
adjacent pair as a two-point block.

For {0,2}, the new local states are {2,4} over one outside configuration and
{0} over the other. For {1,2}, replace {2,4} by {3,6}. In each case the two
cross-context pairs join to the full six-class. A same-context pair leaves
every other five-class split, so cannot join to p+. There are exactly two
top-joining pairs; the triple also joins to p+. The coefficient is -2+1=-1.

For {0,1}, the two groups are {2,4} and {3,6}. The only top-joining pairs are
{2,6} and {4,3}. The other two cross-context pairs leave the six-class split;
the two same-context pairs leave the other classes split. Every triple and
the quadruple join to p+, giving -2+4-1=+1. Individual generators are proper
because every other class is split. These are the complete subset sums.

Joins on other classes are full for each cross-context pair because a join b
was full, and insertion changes only the distinguished class. These facts
establish the stated ORIGINAL coefficient, not merely a local Euler surrogate.

Finally, inflation preserves NCConnected: proper coarsenings correspond by
class labels, and duplicating one position beside an equal-labelled position
does not change the existence of an alternating pair of distinct labels.
This observation is a paper argument, not a newly claimed Lean bridge.

## Formalization scope

AdjacentInflationKernel.lean proves the finite chord identity directly from
localNC5Color/localNC6Color, then lifts it to arbitrary context types X and
arbitrary outside constraint relations R. It proves that a complete two-tuple
family excludes the two universal states and records the 3/4 lift cardinality.

FourGeneratorPositiveCoefficient.lean proves a general original-coefficient
lemma: four complete proper generators whose only top-joining pairs are the
two disjoint pairs contribute +1. It does not assert realizability in a size
profile. The three-generator -1 lemma was already verified in PR43.

The unresolved FORMAL obligation is an original-position gap encoding that
satisfies this abstract context specification, followed by the join transport.
The paper argument above discharges the mathematics, but the local Lean
kernel must not be reported as the whole game theorem being Lean-certified.

## Independent tests and bounded falsification

check.py derives the same map from original blocks in a separately ordered
Python catalogue and checks all 280 actual two-class interleavings (56 layouts
with the first three positions distinguished, times five outside certificates).
It independently evaluates the three possible abstract signed-join kernels.
The +1 kernel is synthetic: its displayed generators are not asserted to be
the complete original family of the displayed two-interval target pattern.

search30.cpp inserts a new five-class in all choose(30,5)=142506 layouts over
each of the 767 previously verified n25 marked representatives. It uses the
complete two-certificate source families and the original interleaving table
to compute all permitted new choices. Two distinct singleton choices, one
over each source configuration, give a complete two-generator survivor. It
also verifies that the new class crosses an old class, preserving connectivity.
Other candidate types cannot have full join or a complete two-generator family.

This checks 109302102 completion cases and finds 40472 survivor completions,
with ZERO uncovered adjacent pairs in the newly inserted class. Counts are
completions, not distinct patterns. The parent representatives are not expanded
under every symmetry, and this is NOT an exhaustive n30 survivor census.
Existing-class adjacency cannot be created by insertion; all input fixtures'
adjacent pairs are independently checked against their two certificates.
replay30.py independently regenerates the complete families for the FIRST64
positive completions and verifies all their adjacency properties and coefficients.
It does not independently replay all rejected completions. The bounded null
result supports the obstruction conjecture; it is not its proof.

## What remains

A concrete next target is: every adjacent equal pair in a connected all-five
two-generator survivor is a pair-block of one generator. Proving this would
settle uniform adjacent-inflation preservation for these survivors. It would
NOT classify all first-excess survivors: the exceptional two-generator cases
from the n16/n21 censuses and higher excess remain outside that construction.
The original full counting problem is still open.
