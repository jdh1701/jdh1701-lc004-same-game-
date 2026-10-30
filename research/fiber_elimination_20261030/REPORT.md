# Classwise separators and five-row elimination

The general fixed-alphabet Same Game enumeration problem remains **OPEN**.
This continuation proves a smaller canonical Euler model for every original
pattern, and an exact five-row elimination law whenever one class has size five.
It also replaces the 44 difficult mixed (5,6) zero values by explicit structural
cancellation certificates.

## Formal results

Write c(p) for the original `winningJoinCoefficient`, and let
beta(F) = sum over faces s in F of (-1)^|s|. The empty face is included when it
belongs to F; an empty face family has value zero. These conventions also cover
patterns with no certificate refinements.

1. **Classwise binary cuts suffice for every pattern.** For each original class,
   split it into two nonempty parts and leave every other class intact. Let V(p)
   be the deduplicated set of these proper refinements. For an original
   noncrossing pair/triple certificate c below p, put
   S_c = {v in V(p) : c <= v}, and let F(p) be the union of their face simplices.
   Then c(p) = beta(F(p)). No class-size, connectivity or noncrossing assumption
   on p is required. Lean: `winningJoinCoefficient_eq_class_cut_face_sum` in
   `LC004/ClassCutSeparators.lean`.
2. **A five-point class has precisely five possible certificate rows.** Restrict
   any original certificate to the five ordered positions. Its noncrossing
   pair/triple partition is one of 00011, 00110, 00111, 01100, 01110. Exactly one
   local binary cut lies above that restriction. The other ten proper cuts of
   the five-point class never occur in a certificate facet. Lean:
   `original_certificate_unique_five_row`, with the complete finite local
   classification checked by the kernel.
3. **Exact five-row formula.** Let M be those five active cuts, P the subcomplex
   of F(p) avoiding M, and L_s the link of active cut s. Then

   c(p) = beta(P) - sum_(s=0)^4 beta(L_s).

   Every other class may have arbitrary size. The theorem uses an increasing
   embedding of the selected five positions, with hypotheses saying they form
   one complete original class. Lean:
   `winningJoinCoefficient_five_rows_class_cuts` in
   `LC004/FiveClassSeparatorElimination.lean`. The version
   `winningJoinCoefficient_five_row_formula` works with any proper cofinal
   separator family.
4. **Combinatorial cancellation criterion.** If P equals one row L_s and every
   other row has an explicit common vertex, the coefficient vanishes. The
   equality of face families and the common partners are the hypotheses;
   cancellation is not assumed numerically. Lean:
   `faceAlternatingSum_zero_of_dominant_row` in
   `LC004/ExclusiveSeparatorElimination.lean`.

### Why the reduction is valid

For any proper refinement r < p choose a,b with p(a,b) but not r(a,b). Within
that original class, divide points by whether r(a,x) holds. This is a nontrivial
binary cut q, and r <= q < p. Thus the classwise family is cofinal among all
proper refinements. Applying the existing original-coefficient face-sum theorem
proves result 1. This argument also handles the boundary case where there are
no proper refinements.

A certificate restricted to a saturated five-point class is a noncrossing
partition into blocks of size two or three, hence one pair and one triple. A
nontrivial binary cut constant on both blocks must separate exactly those
blocks. The five local possibilities are distinct, so a certificate facet has
exactly one marked vertex. Consequently every face either avoids M or contains
one unique member s of M. Erasing s changes its alternating sign and gives the
link L_s bijectively. Summing this disjoint partition proves result 3. A common
vertex gives sign-reversing insertion/deletion in a row, so all nondominant rows
vanish, and the dominant row cancels P. This proves result 4.

There are mathematically sum_C (2^(|C|-1)-1) distinct classwise cuts for nonempty
classes C. This cardinality formula is an explanatory paper observation, not a
new Lean cardinality theorem. The Lean definition deduplicates an indexed family;
it is not advertised as an efficient executable enumeration implementation.

## Free-interval theorem and a failed bounded strategy

`LC004/FreeIntervalElimination.lean` adds a further checked reduction. Suppose a
face sigma lies in exactly one facet tau and tau contains a vertex w outside
sigma. All cofaces of sigma form the Boolean interval [sigma,tau]. Toggling w
pairs opposite signs, so removing that entire interval preserves beta. The
remaining complex is represented sparsely by replacing tau with tau minus v for
each v in sigma. Both the alternating-sum theorem and that exact facet identity
are proved in Lean; `winningJoinCoefficient_remove_free_interval` applies the
reduction directly to the original coefficient on the canonical class-cut family.

This distinction matters for the PR39 cores: all 17 have a generalized free
triangle, even though three have no codimension-one elementary free pair with
lower dimension at most two. The first diagnostic incorrectly conflated these
notions; its failed assertion and source are retained in
`pr39-core-crosscheck.*`. That stronger no-free-triangle assertion is KILLED.

We tested a deterministic lexicographic rule removing free intervals whose lower
face has at most three vertices. All 1,438 removals were independently replayed
against complete coface incidence, removing 23,624 faces; the largest interval
contained 128 faces. **All 17 cases then stalled.** This particular greedy rule
is therefore not a complete construction on these examples. Stalling does not
refute another order or another reduction: PR39 already supplies full elementary
collapse traces. `free_intervals.py` and all traces preserve this negative result.
No general theorem that triangle intervals always suffice is asserted.

## Independent finite checks

| Check | Exact scope | Result |
|---|---|---|
| `class_cut_check.py` | All 1,156 set partitions of n=0..7; 21,052 proper-refinement incidences | Strictness, cofinal coverage and original-coefficient equality pass |
| `fibers.py` | 4,315 distinct prior original patterns; 6,115 selected five-class eliminations | Every reconstructed five-row value equals the previously computed coefficient |
| `mixed_certificates.py` | All 44 full-generator-join zero patterns of profile (5,6) | 33 dominant-row certificates; 11 collapsible-projection certificates with cone rows |

The mixed replay independently generates all 495 global noncrossing pair/triple
certificates at length eleven, filters them on original positions, constructs
actual class cuts, and checks the original signed-join coefficient. It does not
use the local compatibility table to construct its cancellation certificates.
The generic cancellation theorem is formal; these 44 stored instances are
VERIFIED-COMP, not 44 newly instantiated Lean theorems.

Among the full-join (5,6) cases, the five-row signatures are:

| Generators | Original coefficient | Projection beta | Sorted row betas | Cases |
|---|---|---|---|---|
| 16 | 0 | -1 | -1,0,0,0,0 | 22 |
| 3 | -1 | -1 | 0,0,0,0,0 | 22 |
| 12 | 0 | -1 | -1,0,0,0,0 | 11 |
| 7 | 0 | 0 | 0,0,0,0,0 | 11 |

## Larger falsification search

`stress.py` tests all positive six-run compositions for profiles (7,9), (8,10),
(7,10), (6,11), plus the 32 previously budget-skipped cases. All 451 earlier
crossing (5,6) patterns first pass a comparison of generators, joins and Euler
values with the independent baseline. The 2,198 new/reattempted cases comprise:

- 1,120 evaluated full-join cases;
- 1,008 proper-join cases (original coefficient zero by the existing theorem);
- 57 five-second time-budget skips;
- 13 reduced-face-budget skips.

Of the 32 old skips, 31 now have exact coefficient values and one remains skipped.
There are 326 evaluated full-join zeros. Reduced F2 homology was computed in 325
of them; all 325 are acyclic. No counterexample was found. This is only a
necessary-condition test for collapsibility: acyclic does not imply collapsible.
The remaining zero, word 001100000001111111 of profile (9,9), has 3,591 generators
and a strongly reduced complex with 34 vertices and 864 facets. Its exact Euler
value was obtained by the earlier memoized decision version; homology was not
computed in this run. Subsequent repository reconciliation found this exact case
already resolved by PR39; see below. It is not an open finite case anymore.

The search resumed across implementations: the earlier exact decision values
were retained when later stages switched to bounded face enumeration and
zero-only homology. Every earlier script/checkpoint/log is archived. In the final
script a fresh invocation starts empty; `--resume` explicitly reuses a checkpoint.
Timeout classifications can vary with machine load. The fixed archived results
are the evidence for these stated counts; they are not a claim that all cases
fit the current per-case budgets from a fresh start. Caps are 30,000 faces and
3,000 faces for homology. The reported final invocation time is not cumulative.

## Reconciliation with parallel PR39

Before finalizing, a fresh repository check found PR39 at head
495dce2e54aed507394c5e55707dee9e11de8668. Its exact source
81bca891be8f9f7534444a3fb3cbc9073171af4a passed both jobs of hosted run
41002449977, as independently checked through the job API here. It resolves all
32 earlier budget skips: 26 zeros have replayed collapses and the six survivors
have coefficients 8, 10, -4, twice each. Its census and ours overlap; totals must
not be added, and rescuing those cases is credited to PR39.

In particular, 001100000001111111 is **already computationally certified
collapsible**, with 54,528 faces after the recorded domination sequence. The
remaining useful question concerns a uniform geometric rule, not that finite
case. Its retained core has no elementary free pair whose lower face has
dimension at most two; a dimension-three lower face is needed to start the
recorded elementary procedure. This is a statement about that residual complex,
not all domination orders or all possible decomposition methods.

The pinned PR39 report, receipts, source snapshots and our replay evidence are
retained in this archive. We locally reran all32 rescues and matched all31
overlapping coefficient values from our search. The source materialization added
one trailing blank line; archived snapshots match the remote Git blob hashes
exactly. The frozen compressed receipt comparison ran in PR39 hosted CI, not
locally, because the connector rejected its binary download. The new universal class-cut and five-row Lean theorems
are separate from PR39, which reuses the older generic collapse implication.

## Verification, reproduction and limits

The full local Lean build passes with **236 active modules and 3,987 audited
project declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
Coverage, placeholder/source guards and both negative guards pass. The previous
PR38 source f919410e300e724914913e862f551967c989a5f6 now has hosted SUCCESS for both
jobs in run 40998017137. New exact-source hosted status is recorded separately in
`receipts.json`; until green, use PROVED-PAPER with local Lean verification.

From the repository root:

```sh
python research/fiber_elimination_20261030/restore_baseline.py
python research/fiber_elimination_20261030/class_cut_check.py
python research/fiber_elimination_20261030/fibers.py
python research/fiber_elimination_20261030/mixed_certificates.py
python research/fiber_elimination_20261030/free_intervals.py --archive-input
lake build LC004
lake env lean scripts/AxiomAudit.lean
python scripts/check_lean_coverage.py
python scripts/test_verification_guards.py
```

The restore checks archive and member SHA256 values and refuses to overwrite a
differing local file. Hosted CI runs the three original-pattern checks, the free-interval replay, and the full Lean
audit. The longer stress search is separately reproducible with `stress.py` and
is not claimed to run in the short replay job. All raw evidence, failed Lean
attempts and interrupted searches are in `evidence.tar.gz`, with per-member hashes
in `evidence_manifest.json`.

The formula is an exact reduction on a given original pattern. It does not
supply a bounded-state recurrence counting row families over all words, a closed
form for connectedGameWeight, or a general collapse theorem. Those are still
open. No worldwide novelty claim is made.
