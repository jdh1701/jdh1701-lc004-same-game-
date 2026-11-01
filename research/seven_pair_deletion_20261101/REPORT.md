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

## 5. Polynomial evaluation on the proved strata

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
law remains invalid even under a nonzero-coefficient hypothesis. Nor do these
results classify all universal-seven survivors as singleton triplings; that
stronger exhaustiveness claim is deliberately left unproved. Multiple
six-classes, arbitrary higher profiles, and all-length enumeration remain open.
