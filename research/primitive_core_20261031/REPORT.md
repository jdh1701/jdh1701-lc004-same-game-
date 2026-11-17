# Common certificate gaps and the all-five primitive core

2026-10-31, America/New_York. Base: PR46 at
243b4eaece18df07e205bcd31df22a1c536aee10.

## What is proved, and what remains open

**PROVED-PAPER:** every five-point class of a nonzero, nontrivial connected
all-five pattern has exactly three cyclic runs, with lengths **(1,2,2)**.
This discharges the run-shape question left open in PR46, for every number of
classes. It yields a bijection with strongly connected two-layer three-vertex
star cores, and an exhaustive enumeration algorithm on 3j rather than 5j
positions. The algorithm still has exponential growth; no closed formula or
polynomial-time claim is made.

Let A_j count the nonzero connected all-five patterns on 5j labeled cyclic
positions, j>=2. The number H_j of nonzero connected (6,5,...,5) patterns with
a three-run is now determined uniformly:

    H_j = 2(5j+1) A_j / 5.

Every pattern counted by H_j has a unique three-run, exactly three original
certificates, and coefficient -1. This is a specified layer, not the complete
first-excess family. The exceptional no-three-run families, higher excess,
and full A035617 winning-word enumeration remain **OPEN**.

The new Lean module targets the common-gap lemma in both circular cases and
the finite five-state facts. The full run-shape/core/count assembly is a paper
proof. Formal status and exact hosted pins are recorded separately; no local
Lean runtime is available. Neither the complete paper assembly nor the C++
search is being labeled a kernel-checked theorem.

**Final hosted verification:** source
464f98e0996dfea5e9c79bb98bccfb0daa03521b, run41222379964, Lean124599458558
and exact124599458416 both completed/SUCCESS. All247 modules build and all4164
project declarations pass the standard-axiom audit; both negative guards pass.
The common-gap lemmas, adjacency corollary and finite catalogue facts are now
**PROVED-LEAN**. All1,522,974 complete original-family replays and all recorded
hashes reproduce at that source. The first failed arithmetic elaboration and
both complete final job logs are archived with hashes in receipts.json.

## 1. A common chord forces an empty class gap

Let F be a finite family of noncrossing partitions refining p, with join p.
Suppose p is NCConnected (its least noncrossing coarsening is the one-class
partition). Let u,v be consecutive occurrences of a p-class in circular order,
and suppose every c in F identifies u,v. Then the open circular gap from u
to v is empty.

First consider u<v and the ordinary interval I=(u,v). No point of I has
the color of u. If c relates x in I to y outside I, then y cannot equal u
or v: refinement and transitivity would put x in their p-class. The chords
u--v and x--y strictly alternate. Noncrossingness of c then identifies x
with u, again contradicting refinement. Thus I is saturated under every c
and consequently under their join p. If I were nonempty, the partition
{I, I-complement} would be a proper noncrossing coarsening of p. Both parts
are nonempty because u lies in the complement. This contradicts NCConnected.

For the wraparound gap, let u be the smallest and v the largest occurrence
of the selected p-class. The same alternating-chord argument shows the closed
interval [u,v] is saturated under each c. Its complement is the gap. A point
outside [u,v] would again give a proper noncrossing two-part coarsening. The
Lean file proves this directly, without importing a rotation-invariance claim.

This lemma requires the JOIN of the selected family to be p. An arbitrary
shared certificate chord without that premise is insufficient.

## 2. The uniform (1,2,2) theorem

Assume p has j>=2 classes, all of size five, is NCConnected, and has nonzero
original signed-join coefficient. The already proved original all-five law
(`FiveOriginalCoefficientLaw.lean`, with the established crossing/connectedness
bridge) says its COMPLETE original certificate family is {c,d}, with c join d=p,
and coefficient -1. Distinctness holds locally on every class, since equal
local partitions could not join to that full class.

Fix a five-class B. Every local certificate is a noncrossing pair plus triple.
Its pair is one of the five cyclic edges of B. Let P and Q be the respective
pair blocks of c and d. They are distinct. The elementary five-state catalogue
has these two properties, also encoded as finite Lean kernel decisions:

* If P and Q overlap, there is a consecutive class edge {u,v} lying in BOTH
  complementary triple blocks.
* If P and Q are disjoint, each is a consecutive class edge identified by
  BOTH certificates: for example P lies in d's complementary triple.

In the overlapping case the common-gap lemma makes u,v consecutive positions
of the whole board. Both original certificates then belong to T, the restricted
family that puts u,v in a triple. Since the full family is exactly {c,d},
T={c,d}, and its original coefficient at p is -1 (each singleton generator is
proper, while the pair joins to p). PR46's contraction theorem instead gives
kappa_T(p)=0: contracting this adjacent pair gives a connected pattern with
a four-class. Rotation transports the initial-pair theorem if necessary.
Contradiction. Hence P and Q are disjoint.

In the disjoint case apply the common-gap lemma to each pair. Both become
two consecutive positions of the whole board. PR46's paper no-three-run theorem
excludes any run of length at least three in a five-class of a nonzero connected
pattern. Thus these two disjoint pairs cannot merge with each other or with
the remaining singleton. They are precisely two maximal runs of length two;
the fifth position is a maximal singleton run. This proves (1,2,2), and
therefore exactly E(p)=2j equal adjacent edges, without a finite-size bound.

Dependencies are explicit: the original two-generator law and restricted
cancellation have certified Lean versions; the arbitrary-position transport
and no-three-run assembly in PR46 remain paper proofs. The new finite catalogue
and common-gap lemmas do not by themselves formalize this entire assembly.

The same argument has a useful stronger conditional form: in ANY nontrivial
connected pattern whose complete original family consists of two generators
with full join, every five-class has shape (1,2,2), irrespective of the sizes
of its other classes. The all-five hypothesis above was used only to obtain
the two-generator family. Restricted cancellation and the no-three-run theorem
already allow arbitrary other class sizes. This extension supports the separate
two-generator first-excess enumeration begun in the following research folder.

## 3. The compressed objects and their exact recognition

Contract each two-run to one point. Each five-class becomes three vertices:
one root R of weight one and two endpoints U,D of weight two. The class labels
form a proper circular word of length 3j: no adjacent positions have the same
class. Represent c by its triple's arc R--U in an upper layer and d by R--D in
a lower layer. The remaining pair block in each layer is an isolated doubled
endpoint. Thus every class is a three-vertex star, with one arc in each layer.
Upper arcs are pairwise noncrossing, as are lower arcs.

Conversely take such a proper core, and replace U,D by consecutive pairs.
The upper certificate has triple R plus the doubled U, and pair the doubled D;
the lower certificate has triple R plus the doubled D, and pair the doubled U.
These are ORIGINAL 2/3 certificates. An adjacent pair cannot cross another
block. Crossings of two triples are exactly crossings of the corresponding
compressed arcs, since doubling an endpoint preserves their circular order.
The two certificates differ in every class and join to the inflated pattern.

Define the directed graph on classes by

    i -> k iff the lower arc of i crosses the upper arc of k.

This is exactly the raw implication graph of the two original local choices.
All mixed-compatibility failures come from those arcs; the adjacent pair blocks
introduce none. The certified all-five SCC criterion therefore applies: for a
connected class-crossing graph, the COMPLETE certificate family is exactly the
two given choices iff this directed graph is strongly connected. Strong
connectivity also implies class-crossing connectivity; the executable checks
both independently as a redundant guard.

The negative direction has a useful direct witness. A nonempty proper set of
classes closed under outgoing arrows permits choosing the lower state on that
set and the upper state on its complement. Upper/upper and lower/lower pairs
were already compatible; closure rules out every forbidden lower/upper pair.
This gives a third original certificate. The positive direction excluding
local states beyond the two displayed ones uses the existing full SCC theorem,
not merely the binary switching observation.

The two source certificates are unordered. Global upper/lower interchange acts
freely, since they differ in every class. The search fixes the orientation of
the class containing position zero and enumerates each unordered pair once.
The smallest unused vertex anchors each new triple, so class relabeling creates
no duplication. Each ordered triple partition and every root choice is visited;
pruning removes only adjacency or same-layer crossing violations. SCC is tested
only at a complete leaf. These facts prove exhaustive traversal of the defined
core objects, rather than inferring completeness from agreement with known counts.

## 4. Rooted counts, including rotational stabilizers

Let N_j be the number of these accepted unordered-pair cores on labeled circular
positions 0,...,3j-1. Compression and expansion give inverse correspondences of
cyclic orbits. The core's roots and weights are intrinsic to its (1,2,2) runs;
its unordered certificate pair is intrinsic because the family has exactly two
members. Thus both directions preserve the order h of the cyclic stabilizer,
including a symmetry that exchanges the two certificates.

An orbit has 3j/h core roots and 5j/h expanded roots. Summing orbitwise gives

    A_j = (5/3) N_j.

This does NOT assume every orbit has maximal size. Direct expansion and union
of all normalized rotations independently verify the factor through j=5.

PR46 gives H_j=(5j+1)/(5j) times the sum of E(p) over sources. Section 2
now proves E(p)=2j for every source, hence H_j=2(5j+1)A_j/5. No conditional
run-shape assumption remains in that paper count identity.

## 5. Finite results and independent verification

| Classes j | Core length | Strong cores N_j | All-five survivors A_j | Three-run first-excess layer H_j |
|---:|---:|---:|---:|---:|
| 2 | 6 | 3 | 5 | 22 |
| 3 | 9 | 21 | 35 | 224 |
| 4 | 12 | 249 | 415 | 3,486 |
| 5 | 15 | 3,873 | 6,455 | 67,132 |
| 6 | 18 | 70,917 | 118,195 | 1,465,618 |
| 7 | 21 | 1,447,911 | 2,413,185 | 34,749,864 |

The last two A_j counts extend this project's earlier verified range. They
are **NOT A035617(30) or A035617(35)**. The H_j values likewise count only the
specified three-run layer, not all first-excess patterns of lengths 31 and 36.

`check.py` compiles and executes the canonical C++ search for j=2,...,7 and
replays EVERY accepted core through `replay.cpp`. The latter does not use SCC
or the search's arc test. It regenerates all ten pair/triple partitions of five,
retains the five noncrossing ones, computes original-position compatibility
for every two-class interleaving, and exhaustively enumerates the complete
five-choice family by a smallest-domain constraint search. It rejects a third
certificate, requires the exact two expected certificates, verifies full joins,
and separately checks original class-crossing connectivity.

The replay's crossing test uses inside/outside counts relative to each chord;
the search uses alternating endpoints. These implementations are separate but
encode the same mathematical criterion. Positive replay cannot alone establish
absence of false negatives: that relies on Sections 1-4 and exhaustive traversal.
To test that different risk, a Python certificate-first census generates every
NC certificate with j pairs and j triples for j=2,3, matches pairs with triples
in all ways, computes ORIGINAL signed joins on every connected feasible pattern,
and compares the complete survivor sets with expanded cores. It uses no SCC or
run-shape pruning. All core rotations are also unioned explicitly for j<=5.

Eight deterministic samples per size (or all if fewer) are checked again by the
older Python catalogue/alternating-endpoint/original-signed-join implementation.
Those samples are a partial third check, not an independent complete census.
All shared cyclic class edges in nontrivial connected joins of pairs of original
certificates through length ten are also checked, including wraparound edges.

The stable JSON records counts and SHA256 of every full witness stream. Huge
witness streams are regenerated and replayed, then discarded; small deterministic
samples are retained. Timings are deliberately excluded from reproducibility
comparisons. Reproduce with:

    python research/primitive_core_20261031/check.py

## 6. Failed route and research reconciliation

Connected proper star pairs alone are NOT a recognition theorem. At j=4 there
are 357 connected proper unordered pairs but only 249 strongly connected ones.
The retained explicit counterexample has THREE original certificates and zero
coefficient; see `FAILURES.md` and `checks.json`. Applying the 5/3 weight before
SCC filtering would give a false answer. This failure is useful: the obstruction
has been isolated as a genuine global implication condition, not local run shape.

PR35 advanced from b0e3f9e4982edf374cc64574b2c8bd7867094903 to
c88cc0906591ad2b79cdeb168f04a77bf5950553 with a 55-line WORKBOARD review of PR45,
and no new Lean proof files. Claude read those two PR45 modules, found no gap,
and confirmed the pinned CI status. That review does not cover PR46 or this
new proof. PR41-46 had no newer proof changes at the reconciliation check.

Primary literature checked: [OEIS A035617](https://oeis.org/A035617), Kurz's
2001 [same-game polynomial note](https://oeis.org/A035617/a035617.pdf), and
Burns/Purcell's 2007 [binary counting paper](https://www.fq.math.ca/Papers1/45-3/burns.pdf).
The binary problem is a different restricted result; the old OEIS comment
about three or more symbols is not an exhaustive certification of present-day
openness. None supplies the missing general enumeration in the work reviewed.
Exact-sequence searches gave no pertinent match; this is not evidence of novelty.

The next unresolved structural target is the exceptional first-excess family
without a three-run, followed by arbitrary higher-excess connected components.
The full problem is not solved by renaming an exponential boundary-layer search.
