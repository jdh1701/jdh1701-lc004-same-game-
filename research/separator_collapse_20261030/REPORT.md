# Mixed-profile separator collapse frontier

Research date: 29 October 2026, America/New_York. Objective: the unresolved general Same Game winning-word enumeration problem, including A035617.

## Reconciliation and scope

This continuation starts from PR37, source branch proof/mixed-kernel-obstructions-20261030 at 482ff9f3e678aaf7cf120a0974613c18fbb5676d. Its mathematical source equals proof commit ba744372317983ce26c94e32d7f7cd176c4893ac: GitHub comparison shows only evidence/documentation changes. Hosted run40994461526 has now completed successfully, superseding the earlier in-progress receipt. The unconditional original-game separator/Euler bridge is therefore available as a checked foundation.

The new isolated branch is research/separator-collapse-census-20261030. No integration branch or existing Lean module is modified. Earlier personal-context summaries of unpublished experiments are not used as verification evidence. The repository already contains a sampled (5,7) Mobius experiment; positive coefficients there are not claimed as a first discovery here.

## Mathematical object

For a fixed color pattern p, take all original noncrossing pair/triple certificate partitions refining p. For each original color class, use every nontrivial unordered two-part cut of that class as a separator vertex. A certificate facet contains precisely the cuts that it refines. The complex K(p) is the union of the simplices on these facets, with the empty face included whenever at least one certificate exists.

The previously proved original-game identity gives

    winningJoinCoefficient(p) = sum_{S in K(p)} (-1)^|S|.

This is minus the reduced Euler characteristic for a nonvoid complex. It counts a signed coefficient of a fixed pattern, not winning words or deletion histories. These coefficients feed the existing exact counting polynomial; evaluating and enumerating them uniformly remains unresolved.

A common proper refinement of every generator already forces coefficient zero. We focus on the harder cases where the join of all generators is p. Generator completeness is compared for EVERY crossing input between two algorithms: classwise local NC catalogues with cross-class crossing tests, and an independent global first-block interval recursion on the actual word.

## Exhaustive finite result

Ten class-size profiles were checked: (4,6), (4,7), (4,8), (5,6), (5,7), (5,8), (6,6), (6,7), (6,8), and (7,7). Equal-size profiles retain only the class containing position zero, removing the color-swap duplication. Unequal-size profiles distinguish the smaller class, which also represents each unlabeled equality pattern once.

There are 10,473 distinct two-class patterns, of which 10,364 are crossing. Exactly 1,156 crossing cases have zero coefficient despite a full generator join. EVERY one collapses to a point by elementary free-face collapses. Every collapse step was independently replayed using global coface incidence, rather than trusting the codimension-one data structure used to find it. Per-pattern trace hashes and full first-example traces are retained in census.json.gz.

| Sizes | Crossing patterns | Full-join zeros | Independently replayed collapses |
|---|---:|---:|---:|
| 4,6 | 200 | 15 | 15 |
| 4,7 | 319 | 22 | 22 |
| 4,8 | 483 | 30 | 30 |
| 5,6 | 451 | 44 | 44 |
| 5,7 | 780 | 72 | 72 |
| 5,8 | 1274 | 117 | 117 |
| 6,6 | 456 | 53 | 53 |
| 6,7 | 1703 | 208 | 208 |
| 6,8 | 2989 | 364 | 364 |
| 7,7 | 1709 | 231 | 231 |

This supports a uniform collapse mechanism for zero coefficients. It does NOT prove it for untested profiles or three or more classes. A stalled greedy collapse would be recorded as inconclusive unless a homology obstruction were found; no stalled case occurred in this census.

## A higher-dimensional survivor

The (7,7) pattern 00001001101111 has twenty original certificate generators and coefficient -4. Its separator complex has reduced Betti vector beta_2=4, all other reduced Betti numbers zero, over F_2. This is an explicit higher-dimensional survivor, rather than a zero case.

Independent checks agree:

1. Alternating face sum of the complete separator complex.
2. Signed joins of actual local partition refinements, which preserve the original joins classwise.
3. Partition-lattice Mobius inversion of an independent raw maximal-run solver over every no-singleton refinement (26,244 for this witness).
4. Matching mod-two homology of the original separator complex and its independently constructed facet-incidence nerve.

Nonzero second homology excludes a homotopy equivalence with a one-dimensional graph. It does not exclude graph-based encodings with higher-dimensional reconstruction, or a compact scalar counting identity. Homology alone does not establish a wedge-of-spheres homotopy type.

Examples with coefficients +2 and +6 have corresponding first homology in the selected witnesses. No general classification of all survivor homology types is asserted. As another warning against overinterpreting Euler characteristic, the single six-point local complex has reduced beta_0=3 and beta_1=2, despite its coefficient being only -1.

## Verification boundaries

The complete finite census is VERIFIED-COMP. All classwise generator sets agree with the global recursion. Signed-join evaluation is exhaustive for total size at most twelve; larger profiles use a bounded set of independent join checks including every newly encountered coefficient value. Every selected nonzero witness is independently checked by raw-game Mobius inversion, and original/nerve homology agrees. A circle plus an isolated point is a negative control: its Euler sum is zero but its reduced homology is nonzero, so the program must not declare it collapsible. A cone is a positive collapse/replay control. Boundary spheres in dimensions zero through four give the expected homology.

Both homology calculations use the same exact GF2 elimination routine on independently constructed boundary complexes. They are not two independent implementations of linear algebra. The separate raw-game calculation supplies an independent coefficient check, not a separate proof of every Betti number. No floating point, fitted sequence, or learned classifier is used.

CollapseCriterion.lean proposes a reusable formal route: paired-face erasure preserves the alternating sum; so does a finite sequence of actual elementary collapses; a point complex has sum zero; therefore a collapse of the ACTUAL indexed separator complex certifies zero of the ORIGINAL winningJoinCoefficient for any profile. The free-face condition is explicit. This is a sufficient criterion, not a proof that every zero case admits a collapse. Hosted run40999056173 passed the complete exact census and independent checks. The initial Lean attempt failed only in point_sum because the finite-pair sum did not simplify; the axiom guard rejected its incomplete elaboration. The revised source explicitly applies Finset.sum_pair. Its final compiler/axiom status must be taken from the corrected-source hosted run linked in the PR, not inferred from the Python census. It was submitted as a candidate because workspace maintenance removed the prior local Lean installation.

## Strongest surviving research target

For winning crossing-connected heavy patterns whose original certificate generators have full join, investigate whether zero coefficient forces an elementary collapse of the actual separator complex to a point. The converse is the formal criterion above. The winning/nonvoid qualification matters: a losing word has an empty generator family and a void complex, so Euler zero alone cannot imply a collapse to a point.

A proof must construct a uniform free-pair rule from the geometry. Checking every case of another fixed profile is not a substitute. The next step is to inspect the retained collapse traces for such a rule, then test it on a new three-class or larger-class family. Separately, the surviving nonzero patterns still need an enumeration law. Even a complete zero classification would not by itself solve A035617.

## Reproduction

    python3 research/separator_collapse_20261030/probe.py --profiles '4,6;4,7;4,8;5,6;5,7;5,8;6,6;6,7;6,8;7,7' --output research/separator_collapse_20261030/census.json
    python3 research/separator_collapse_20261030/independent.py
    lake build LC004.IncidenceFaceSum
    lake env lean research/separator_collapse_20261030/CollapseCriterion.lean

The committed archive is deterministic gzip JSON with timing fields removed. Full traces for representative zeros and hashes for all zero-case traces are included. Recompute traces with the source to verify every hash. Standard-library Python suffices. No local Sage or Lean pass is claimed in this continuation, and no worldwide novelty claim is made.
