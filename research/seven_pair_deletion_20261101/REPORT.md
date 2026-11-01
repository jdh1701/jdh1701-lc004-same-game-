# Seven-class deletion and an iterated coefficient multiplier

2026-11-01. Continuation of PR50, base a67850cafbf958447f9d8f58104bc349f6ae0061.

## Result and scope

**PROVED-PAPER.** For a nontrivial NCConnected pattern with a distinguished
seven-point class H, the original join coefficient satisfies

\[
 \kappa(p)=\mathbf1_{u=0}\,\beta(P)
       -\sum_{e\in E_H^\times}\kappa(p\setminus e).                 \tag{1}
\]

Here u counts the local seven-certificates avoiding every outside FULL color
class. P is the projection of the complete original separator complex onto
the outside separator vertices. The set E_H^times consists of globally
cyclically adjacent pairs in H for which the remaining five points of H
cross an outside full class. Other color classes can have ANY sizes.
Deletion preserves cyclic order and uses the induced color partition.

When u>0, the projected term disappears. In particular, this evaluates the
entire universal-certificate stratum of connected (7,5,...,5) patterns by at
most seven all-five coefficient evaluations, with no bound on the number of
classes. A polynomial evaluator is included.

**The universal-seven stratum is also classified on paper:** with every other
class of size five, its nonzero patterns are exactly singleton triplings of
connected all-five survivors. Every coefficient in this stratum is +2. The
proof below excludes other universal-seven run shapes; it does not apply to
the no-universal branch.

A second consequence is a uniform multiplication rule. If a five-point class
has cyclic maximal runs (1,2,2), replacing its singleton point by three
consecutive points multiplies the coefficient by -2. This holds in every
nontrivial NCConnected pattern, with arbitrary outside class sizes, including
zero coefficients. Repeating it on s classes of an all-five survivor gives
coefficient (-1)^(s+1) 2^s and profile (7 repeated s times, 5 repeated j-s times).

These are coefficient results, not a solution of LC004/A035617. They neither
evaluate the no-universal projected term beta(P) nor enumerate every mixed
profile. The whole all-length three-color winning-word problem remains OPEN.

## 1. Small-refinement gap lemma

Let p be NCConnected. Refine one of its classes, keeping every outside class
whole, to a pattern q. Suppose a q-block A has at most four points, and includes
two cyclically consecutive occurrences u,v of the original distinguished class.
If kappa(q) is nonzero, u,v must be globally cyclically adjacent.

Proof. The general original-coefficient support theorem says A cannot cross
any other q-class. If an outside p-class meets the open gap (u,v) and its
complement, it remains whole in q and crosses A, a contradiction. Thus the
gap is a union of entire p-classes. The gap and its complement are cyclic
intervals, so a nonempty gap would give a proper noncrossing coarsening of p.
NCConnectedness excludes it. The same argument treats the gap through the
end of the linear order. No rotation invariance of the coefficient is needed
for the Lean proof.

`LC004/SmallRefinementGap.lean` formalizes this lemma and its vanishing
contrapositives in both ordinary and wraparound positions. It uses the original
`winningJoinCoefficient`, not a surrogate complex. Formal status is recorded
in receipts.json only after an exact-source hosted build and audit.

## 2. Reduce every seven-boundary correction

Use PR50's seven-cut Euler identity, with FULL outside separator complexes:

\[
 \kappa(p)=\beta(P)-\sum_t\beta(K_t)
              -\sum_{c\text{ of type }(3,4)}\beta(E_c)
              -\sum_{c\text{ of type }(2,5)}\beta(E_c).             \tag{2}
\]

There are 21 local states t, seven (3,4) cuts and seven (2,5) cuts. The latter
cuts isolate precisely the seven pairs consecutive in H's cyclic order.
The proof depends only on this local incidence and additivity of beta; it
does not require five-point outside classes. Every correction is the original
coefficient of the indicated refinement of H. The choice-coordinate model
for the new four- or five-block is exact, while outside separator vertices
remain the full ones. See PR50 for the inclusion-exclusion derivation; it does
not interchange intersections of face complexes with common full assignments.

Write B=kappa(p with H deleted), and let v count (3,4) cuts whose two blocks
avoid all full outside classes. Crossed-small-class vanishing and noncrossing
component factorization give

* beta(K_t)=B for a universal state, and zero otherwise: each of its blocks
  has size two or three and isolated coefficient 1.
* beta(E_c)=-B for a universal (3,4) cut, and zero otherwise: the isolated
  four-block has coefficient -1.
* A (2,5) correction is zero unless its pair is globally adjacent, by the
  small-refinement gap lemma. For a globally adjacent pair e, its coefficient
  is kappa(p minus e): the pair is an isolated noncrossing component of weight
  1. This uses coefficient factorization and order restriction, including a
  pair through the cyclic boundary.

It follows that

\[
 \kappa(p)=\beta(P)+(v-u)B
               -\sum_{e\text{ globally adjacent in }H}\kappa(p\setminus e).
                                                                    \tag{3}
\]

The deleted patterns need NOT be connected. Factoring them before using a
connected coefficient law is essential.

## 3. Cancel the universal terms exactly

For each full outside class, partition H by its cyclic gaps; let R be the
meet of those partitions. Each gap partition is noncrossing, as is their meet.
An H-block avoids all outside classes exactly when it lies in a cell of R.
Since p is nontrivially connected, H is crossed; hence R is proper.

If a 2/3 certificate refines R, no cell of R is a singleton. On seven points
the only proper possibilities are (2,2,3), (3,4), and (2,5). Let w be the number
of universal (2,5) cuts. Counting refinements in each cell gives the table:

| R | u | v | w | 1+v-u+4w |
|---|---:|---:|---:|---:|
| (2,2,3) | 1 | 0 | 0 | 0 |
| (3,4) | 2 | 1 | 0 | 0 |
| (2,5) | 5 | 0 | 1 | 0 |

If no certificate refines R, u=v=w=0, because each of either kind of cut has
a 2/3 refinement. If u>0, one fixed universal H-state extends EVERY outside
certificate, so P is the complete outside complex and beta(P)=B.

Every universal (2,5) correction equals -4B by component factorization:
the isolated two-block has coefficient 1 and five-block coefficient -4.
If its pair is not globally adjacent, the correction is also zero, so in
that case B=0. Thus the sum over globally adjacent universal pair corrections
is still exactly -4wB; no adjacency is assumed for a universal cut.

For an actual adjacent H-pair the pair itself crosses nothing. Its cut is
universal exactly when the remaining five-set is uncrossed by every full
outside class. Subtracting the universal terms from (3) leaves

    beta(P) + (v-u+4w)B - sum_(e in E_H^times) kappa(p minus e).

The table cancels the first two terms when u>0. When u=0 they equal beta(P).
This proves (1) for arbitrary outside profiles and arbitrary class count.

## 4. Tripling a singleton multiplies by -2

Let p be nontrivially NCConnected and let its distinguished five-class H have
runs (1,2,2). Form p+ by tripling the singleton run. Consecutive duplication
preserves all original full-class crossing relations, so p+ remains connected.
Its H runs (3,2,2) themselves form a universal 2/3 certificate.

Apply (1) to p+. It has exactly four adjacent H-pairs. The two inside the
three-run each delete back to p. Their residual five-class is crossed since
p is nontrivially connected, so both are in E_H^times.

Deleting either of the two entire two-runs leaves a five-class containing
three globally consecutive points. If that class is uncrossed, the term is
not in E_H^times. If it is crossed, take its nontrivial crossing component.
Restriction to this component retains the three-run. The general five-class
no-three-run theorem from `adjacent_contraction_20261031/REPORT.md` makes that
component's coefficient zero, and component factorization makes the entire
deleted pattern's coefficient zero. This theorem allows arbitrary sizes for
the other classes; using only the all-five version here would be insufficient.

Consequently kappa(p+)=-2*kappa(p). This proof does not assume kappa(p) is
nonzero and does not assume a two-certificate family.

Starting with any nonzero connected all-five pattern with j>=2 classes,
the established run theorem gives (1,2,2) in every class and kappa=-1.
Tripling any selected subset of s singleton runs leaves all other selected
five-classes' run shapes unchanged and preserves connectedness at each step.
Induction gives the exact coefficient (-1)^(s+1)*2^s, for every 0<=s<=j.
There is no fixed bound on j or on the excess 2s in this construction.

### Explicit sources for every j>=3

The unbounded family is nonvacuous. Here is a direct primitive star core for
every j>=3, using the already established core/SCC recognition theorem. Index
classes by i=0,...,j-1, on the positions 0,...,3j-1. Put r_i=3i+2 and

    a_0=0, a_1=1, a_i=3i-3 for i>=2;
    b_i=3i+4 for i<j-1, b_(j-1)=3j-3.

Class i has the three positions {a_i,r_i,b_i}. They partition all 3j positions,
and neighboring positions have distinct classes, including the cyclic boundary.
For even i the upper arc is a_i--r_i and the lower arc is r_i--b_i; for odd i
interchange upper and lower. The notation denotes unordered endpoints, including
the final class where b_(j-1)<r_(j-1).

Each layer is noncrossing. Away from the two ends, its long intervals have
length five, disjoint successive starts six apart, and its short intervals
have length two and are either nested in one long interval or disjoint from
it. The first and last intervals have these same containment/disjointness
relations by the displayed endpoints. This also proves the assertion for j=3.

The lower-to-upper crossing graph contains the directed Hamiltonian cycle

    0,2,4,...,(all even indices increasingly),
    (all odd indices decreasingly),1,0.

For example, an interior even i has lower interval [3i+2,3i+4], which crosses
the next even upper interval [3i+3,3i+8]. An interior odd i>=3 has lower
interval [3i-3,3i+2], which crosses the preceding odd upper interval
[3i-4,3i-2]. The first edge uses [2,4] crossing [3,8]; the final edge uses
[1,5] crossing [0,2]. At the turnaround, the intervals are [3i,3i+2] and
[3i-1,3i+1], with their upper/lower roles determined by the parity of the
last index. They strictly alternate in either case. Thus the graph is strongly
connected for every j, not merely the tested range.

Give each r_i weight one and the two endpoints weight two. The resulting
all-five pattern has coefficient -1 by primitive-core recognition. Tripling
all roots now gives a connected all-seven pattern with coefficient
(-1)^(j+1)*2^j for every j>=3. This explicit construction is a paper argument;
it does not strengthen the scope of the hosted Lean certificate.

### Counting this family, including rotational stabilizers

Let A_j count the original connected all-five survivors on labeled cyclic
positions, with color names forgotten. Let T_(j,s) count the family obtained
by tripling a subset of s classes. Then

\[
 T_{j,s}=\frac{5j+2s}{5j}\binom{j}{s} A_j.                         \tag{4}
\]

This is a family identity, not a census of profile (7^s,5^(j-s)). Each seven
class in the image has a unique three-run. Contracting all those runs recovers
both the all-five source and the chosen subset, so the cyclic construction is
bijective. It preserves rotation stabilizer orders: expansion/contraction of
the marked cyclic run word induces inverse orientation-preserving symmetries.
An orbit with stabilizer order h has 5j/h source rootings and (5j+2s)/h target
rootings. Summing this ratio over source-plus-subset orbits proves (4) without
assuming a free rotation action. At j=2 the three counts are 5,12,7, with
coefficients -1,+2,-4. At j=3 they are 35,119,133,49, with coefficients
-1,+2,-4,+8. These are NOT winning-word counts or A035617 terms.

## 5. Exhaust the universal-seven stratum

**PROVED-PAPER.** Suppose p is nontrivially NCConnected, H has seven points,
all other classes have five points, and H admits a universal local certificate.
Then kappa(p) is nonzero if and only if H has runs (3,2,2) and contracting its
three-run gives a nonzero connected all-five pattern. In that event kappa(p)=2.

Here is a proof that addresses all possible universal certificates, including
ones whose blocks are not globally consecutive. Fix one such certificate T,
with pair-blocks A,B and triple-block C.

First, an auxiliary fact: a crossed five-class with a universal local state
forces the original coefficient to be zero, even in a disconnected pattern.
The five-state Euler identity is beta(P)-sum_t beta(K_t). Each fixed-state
correction is zero unless universal, by crossed-small-class vanishing, and
equals the outside coefficient B when universal. The meet R of the outside
full-class gap partitions is proper because the five-class is crossed.
A feasible proper five-point R has profile (2,3), giving exactly one universal
state. It extends all outside certificates, so beta(P)=B and the result is zero.

Apply (1) to p. For an adjacent pair e in that sum:

* If e equals A or B, deleting it leaves a universal pair/triple state on H.
  Since the residual H is crossed by the definition of E_H^times, its
  coefficient is zero by the auxiliary fact.
* If the two points of e lie in different T-blocks, delete them and merge
  the remnants of those two blocks. Their sizes become either 1+1=2 or
  1+2=3, and the untouched block has the complementary size. This is a
  universal noncrossing five-state. To justify the merge, fix any outside
  full block D (or the untouched T-block). The two adjacent deleted points
  lie in the same gap of D. Each of their original T-blocks lies entirely
  in that gap, since T avoids D. So their merged remnants also avoid D.
  The auxiliary fact again gives zero.

Thus any nonzero deletion must remove two points of C. Let r be its remaining
point and q=p minus e. For every full outside class D, all three C-points lie
in one gap of D. Removing two of them while retaining r cannot change whether
H meets more than one gap of D. Hence EVERY full-class crossing relation is
preserved. In particular q remains connected. If its coefficient is nonzero,
the all-five law gives exactly two complete certificates c,d with full join,
coefficient -1, and H runs (1,2,2).

The surviving A,B are noncrossing pairs that avoid every outside full class.
We claim they are exactly the two doubled runs of q, and r is its singleton.
For two noncrossing pairs and a singleton on five cyclic points, either both
pairs are consecutive in the H-order, or one is consecutive and the other
surrounds the singleton in a three-point interval. Any consecutive universal
pair must be globally adjacent, by the saturated-gap argument from section 1
(here avoidance of outside full classes is given directly). In the second
case the consecutive pair is one doubled run of q; the other doubled run must
join r to an endpoint of the surrounding pair. Merging that pair with the
adjacent r then gives a universal triple, by the same gap argument used above.
Together with the consecutive pair it is a universal five-state, contradicting
kappa(q)=-1. Thus only the first case is possible, proving the claim.

Reinsert the adjacent pair e. It cannot lie between the two points of A or B:
then C, containing e inside that pair and r outside, would cross that T-pair.
There are three remaining H-gaps in q. If e is inserted into either gap next
to r, a chord of the universal C joins consecutive H occurrences. The
saturated-gap argument forces actual adjacency to r. Hence C is a three-run.

The final possibility is insertion into the H-gap between A and B, opposite
r. The universal chord from r to e divides all outside FULL classes into two
open intervals I,J, with A in I and B in J; no outside class straddles them.
The local H-parts of c,d are, up to interchange,

    c_H = A | (r together with B),
    d_H = B | (r together with A).

Construct a new certificate with H-state c_H, outside states from d on I,
and outside states from c on J. It is noncrossing: different intervals do not
cross, the pair A is globally adjacent, and the triple r+B lies on the J side.
If I has an outside class, the certificate differs from c there (c and d differ
on EVERY class because their join is q), and differs from d on H. This is a
forbidden third complete certificate. If I has no outside class, J does, since
q is nontrivial. Interchanging I,J and c,d gives the same contradiction.
This excludes the last insertion site.

We have proved that any nonzero deletion in (1) forces p to be a singleton
tripling of an all-five survivor. If kappa(p) is nonzero, at least one deletion
is nonzero, so this proves necessity. Conversely section 4 proves that every
such tripling has coefficient +2. There are exactly two contributing deletions
inside its three-run. The universal state is unique: any universal T in a
nonzero case is forced by the same argument to use the actual (3,2,2) runs.

Consequently the ENTIRE universal connected (7,5,...,5) nonzero stratum with j
classes has (5j+2)*A_j/5 patterns on labeled cyclic positions. This is the s=1
case of (4), now an exhaustive count for this specified stratum. It remains a
properly restricted count; PR50's no-universal +1 witness lies outside it.

## 6. Polynomial evaluation on the proved strata

`fast_coefficient.py` evaluates arbitrary all-five patterns by factoring their
full-class crossing graph. An isolated five-class contributes -4. In a
nontrivial component, the run theorem forces exactly two disjoint two-runs
per class in every survivor. The two possible certificate states are obtained
by using one or the other of these runs as the pair-block; pair coverage in
the complete two-certificate family justifies this restriction.

Find a valid separated pair a, complement(a). For each pair of classes, impose
both original compatibility of their selected states and compatibility of
the complementary states. Each resulting binary relation is complement
symmetric, hence all, equality, inequality, or empty. XOR propagation finds a
solution or proves none exists. If one exists, build the raw forbidden-mix
implication graph and test strong connectivity. The certified theorem
`fiveClass_survivor_pair_iff_strong` says it is strongly connected exactly when
the COMPLETE original family consists of this pair, including exclusion of
all other original local states. Combined with the certified all-five law,
this gives coefficient -1 in the strong case and zero otherwise. An arbitrary
valid separated pair suffices: a survivor has just one such unordered pair.

There are O(j^2) fixed-size compatibility tests and a graph calculation per
component. This avoids enumerating 5^j full assignments. Integers in a product
of isolated-component weights have O(j) bits; the bound on compatibility tests
does not purport to count arbitrary-precision operations as unit cost.

For a nontrivial connected (7,5,...,5) input with a universal seven-state,
`universal_seven_coefficient` applies (1) and at most seven calls to the
all-five evaluator. It returns None outside this proved domain, never an
assumed zero. These algorithms are justified by paper assembly and the cited
formal laws; the Python programs themselves are not Lean-certified.

## Verification, a repaired test, and remaining obstructions

`check.py` compares (1) and (3) with complete original separator face sums,
and with direct original signed-join sums when the complete family has at
most twelve generators. It exhausts connected two-class (5,7),(6,7),(7,7)
geometries, checks specified verified star fixtures, singleton triplings,
repeated triplings, and seeded mixed profiles. All correction terms and cyclic
boundary pairs are checked. `checks.json` gives exact scope and counts.
The repeated-tripling tests use all subsets for j=3, subsets of size at most
two for j=4, and single triplings for j=5; they are not a target census.
The entire j=2 construction is also regenerated with all rotations and direct
original signed-join replays. The two coefficient methods share catalogue
generation, so their independence is partial.

Adversarial review found a weak assertion in PR50's ZERO witness: its target
partition had noncanonical color labels, while the signed-join dictionary uses
canonical labels. The assertion could therefore pass vacuously. The original
script is corrected to canonicalize its target. The zero result remains true
on proper replay. The new checks additionally replay ALL six color relabelings
of the NONZERO +1 witness, preventing this particular vacuity. No theorem or
counterexample value is retracted, and the weakness is retained here explicitly.

The recurrence does not eliminate beta(P) when u=0. PR50's connected (5,5,7)
+1 witness has beta(P)=+1 and all corrections zero, and its projected family
is not majority closed. Thus replacing that term by the previous binary/SCC
law remains invalid even under a nonzero-coefficient hypothesis. Section 5
does classify the universal-seven survivors when all other classes have size
five; it does not classify arbitrary outside profiles. Multiple six-classes,
the no-universal seven branch, arbitrary higher profiles, and all-length
enumeration remain open.
