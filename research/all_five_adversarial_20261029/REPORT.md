# All-five adversarial search and projection formula

Baseline: Claude's >=3-certificate cancellation conjecture; all-five
Fuss-Catalan is already KILLED at n=20 (415 not 285). No retraction of that kill.

VERIFIED-COMP: independently implemented seeded, certificate-conditioned search
at n=10,15,20,25,30. 5200 attempted constructions gave 3575 distinct connected
candidates within their size strata. Of these, 2674 had >=3 certificates and all
had signed coefficient zero; 1058 such cases at n=25 and 1109 at n=30. The
largest certificate family had 625 elements. Both coordinate join aggregation
and the projection formula below agreed on every connected candidate.
CONJECTURE remains: all-five connected patterns with >=3 certificates cancel.
Sampling is deliberately biased toward a known certificate and is not uniform;
no confidence interval or exhaustive claim is warranted. Only two nonzero
sample cases appeared (both n=10); sparse survivors make this a weak support
counting test. Do not present it as an independent reproduction of 35 or 415.
Independent exhaustive n=10 raw-inversion data are used as additional controls.

## PROVED-PAPER: projection formula

Let p have j>=1 classes, each of size 5. Every certificate below p restricts
in each class to a partition into a pair and a triple. Encode the distinct
certificates as a finite relation A of j-tuples of local split choices.
For T subset of [j], let pi_T(A) denote its distinct coordinate projections.
Then the collected coefficient is

  c(p) = sum_{T subset [j]} (-1)^|T| * |pi_T(A)|.

Proof. Any two distinct two-block partitions of the same set have top join:
a proper coarsening of a two-block partition can only be itself. Therefore a
nonempty family S of certificates has join p exactly when, in each coordinate,
the members of S do not all share one split. Inclusion-exclusion on the j
bad events 'coordinate is constant' rewrites the signed generating-subset sum.
For fixed T, the nonempty subsets satisfying all these bad events are exactly
the nonempty subsets within fibers of the projection A -> pi_T(A). Each
nonempty fiber contributes sum_{empty!=S} (-1)^(|S|+1)=1. Summing over fibers
gives |pi_T(A)|, proving the formula. Empty A contributes zero throughout;
for nonempty A the empty-coordinate projection has cardinality one.
This proof uses the established signed-join formula, not the cancellation
conjecture. It holds without noncrossing connectedness assumptions on p.

Equivalent topological statement: make a vertex (i,a_i) for each observed
coordinate/value pair, and a facet {(i,a_i): i in [j]} for each atom vector a.
Its faces on coordinate set T are exactly pi_T(A). Thus c(p) is the negative
reduced Euler characteristic of this j-partite complex. This is a different,
often smaller complex than the earlier complex with certificates as vertices.
No novelty claim: this is a finite inclusion-exclusion/face-count derivation.

Evaluation takes O(2^j * |A| * j) elementary projection work once A is given.
It avoids enumeration of 2^|A| certificate subsets, but generating A remains a
bottleneck. It does not solve the global enumeration or prove the conjecture.
No new Lean theorem is claimed in this checkpoint.

## Next / Claude handoff

Try to prove reduced Euler characteristic zero for these choice complexes when
A has >=3 elements and p is NC-connected all-five. Do not assume contractibility:
Euler characteristic zero is weaker, and topology needs its own counterexample
search. The two-certificate case is a pair of facets; its intersection determines
whether c=-1 or 0. Look for a geometric decomposition/relative matching for
larger A. This changes the target from a huge certificate-subset complex to
at most j coordinates with explicitly recorded allowable tuples.
