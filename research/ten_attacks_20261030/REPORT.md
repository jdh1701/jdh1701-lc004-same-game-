# Ten attacks on exact Same Game enumeration

2026-10-30. Objective: an all-length, tractable enumeration of distinct winning
words over three colors (A035617), ideally any fixed alphabet. The objective is
**not solved**. Speculative attacks were allowed; proof status was not relaxed.
No worldwide novelty claim is made.

## Repository reconciliation

The active development is in `jdh1701/jdh1701-lc004-same-game-`, not the parent
Alexandria presentation repository. This campaign starts from PR37 head
`482ff9f3e678aaf7cf120a0974613c18fbb5676d`; PR35's later changes were checked and
are verification/documentation updates. Its all-five proof is already certified.
PR37's initial source `8837755fa941466fe371ca9df9543adafca182b3` passes hosted
run40994029481. Its full six-module source
`ba744372317983ce26c94e32d7f7cd176c4893ac` now passes run40994461526. This supersedes
the earlier pending status. Other branches were not overwritten or merged.

The current public problem description and 26 terms were checked at
https://oeis.org/A035617 on2026-10-30. That entry still describes the general
b>=3 enumeration as apparently unsolved. The binary result is prior work, not
part of this campaign's claimed progress.

## Ten distinct attempts

| # | Route and proposed route to a full solution | Executed result | Status and remaining obligation |
|---|---|---|---|
| 1 | Scalar algebraic generating equation or polynomial-coefficient recurrence | Exact rational linear algebra tests48 bounded ansatz spaces on26 known terms; none survives. An order10 constant recurrence fit to20 terms fails at n20. | KILLED for the specified bounds only. No claim of transcendence or non-D-finiteness. See analytic.json. |
| 2 | Unique factorization into indecomposable winning words, then a code generating function | Directly enumerated ternary words through n9 and their indecomposables. Free concatenation predicts36 at n5 instead of33. The word00000 has decompositions00·000 and000·00. | KILLED in this form. Selecting a canonical factorization still needs contextual exclusion; it is not an unambiguous counting grammar. |
| 3 | Finite boundary states or a fixed finite-dimensional tensor representation of word acceptance | Proved on paper that (01)^m22(10)^n wins iff m=n. Independently tested the31x31 identity matrix. | PROVED-PAPER obstruction: arbitrary exact word-boundary rank is unbounded. Does not rule out a rational scalar length generating function. |
| 4 | Canonical deletion through a simple local optimization rule | Eight explicit deterministic rules all have counterexamples by length7; the search includes an extra loop-bound check through8. Full words, chosen losing moves and successful alternatives saved. | KILLED for those eight rules, not for every conceivable strategy. |
| 5 | Monotone run-template reliability polynomials and run-length substitution | Exhausted ternary proper run skeletons modulo label permutations through9 runs; recovered W0..W9 exactly. Minimal winning-heavy-set antichains reach12 elements. Equal run/turn/heavy counts do not determine winning. | Exact reduction and finite checks; no bounded-state or tractable recurrence for the reliability polynomials yet. |
| 6 | Replace the complete join hypergraph by pairwise top-join edges and an independence polynomial | A (5,7) pattern has actual coefficient2 but pair-graph prediction1. A separate (5,6) witness has a minimal three-generator top join with no top-joining pair. | KILLED. Higher-order joins are essential. |
| 7 | Discrete Morse cancellation of separator complexes |286 full-generator-join zero cases in the first four profiles collapse by vertex domination. In the larger first holdout,16 stalled cores all collapse by elementary free-face removals. Independent catalogue generation and trace replay pass. | VERIFIED-COMP lead, not a universal classification. The elementary-collapse implication for original coefficient vanishing is proved locally in Lean. |
| 8 | Compress a connected kernel to its class profile and certificate count | Two (6,6) patterns each have4 certificates but coefficients0 and-1. | KILLED, even when the class profile is held fixed. |
| 9 | Strip run lengths to a cyclic crossing core and inflate decorations | Two (5,6) patterns have the same alternating six-run cyclic core and coefficients0 and-1. | KILLED for the undecorated core. A weight-preserving decorated core remains possible. |
| 10 | Exact separator deletion/link recurrence with memoized facet states |3,769 original-pattern checks agree with face sums;142,297 memoized states in aggregate. Largest newly visited state count for one query11,185. Facet normalization and the universal recurrence are proved locally in Lean. | Correct exact method; no polynomial state bound and no all-word enumeration recurrence. |

## Actual positive proofs

`LC004/SeparatorDeletionLink.lean` adds general statements, with no all-five or
fixed-profile assumption:

- `faceAlternatingSum_deletion_link`: beta(F)=beta(delete_v F)-beta(link_v F).
- `separatorDeletion_facetFaces`, `separatorLink_facetFaces` and
  `facetAlternatingSum_deletion_link`: both branches can be represented directly
  by facets without listing all faces.
- `facetFaces_eq_of_mutual_cover`: normalizing away duplicate or contained facets
  preserves the complex exactly.
- `faceAlternatingSum_erase_pair` and `faceAlternatingSum_elementary_trace`:
  the stored elementary-collapse steps preserve the alternating sum.
- `winningJoinCoefficient_separator_deletion_link`: the recurrence applies to
  the ORIGINAL game coefficient through the complete separating-family bridge.
- `winningJoinCoefficient_zero_of_elementary_trace`: an explicit trace from the
  actual separator complex to a point proves original-coefficient vanishing.

These are general infrastructure theorems. The Python collapse traces are
independently replayed finite evidence, not passed off as Lean proofs of every
listed original pattern. The source contains no asserted universal collapse
conjecture. The final audit receipt records build and CI status separately.

## Infinite boundary-rank obstruction: complete paper proof

Let U_m=(01)^m and V_n=(10)^n, for m,n>=0. In U_m22V_n the only initial legal
maximal-run move is deleting22. If m,n>0, the only resulting heavy run is the
central11. Deleting it exposes exactly00. Deleting that gives
U_(m-1)V_(n-1). Repeating the forced central pair deletions strips one01 from
the left and one10 from the right. If the lengths match, nothing remains. If
one side runs out first, the remainder is a nonempty alternating word, with
no legal move. If either parameter is initially zero the same conclusion
holds immediately after22. Thus the original maximal-run winning indicator is
exactly delta(m,n), for all m,n. No triple or alternative move arises anywhere
in this forced sequence.

For every d, prefixes U_m22 and suffixes V_n,0<=m,n<d, therefore give an identity
submatrix of size d in the word Hankel matrix H(u,v)=1[uv wins]. Its rank over
any field is at least d. Any representation alpha*M_word*omega with a fixed
D-dimensional state has every such submatrix of rank at most D, so cannot
represent this language. A deterministic finite automaton is a special case;
alternatively the suffixes distinguish every pair of these prefixes directly.
This argument does NOT imply that the scalar sequence W_n lacks a rational or
algebraic generating function: summing over words can erase the distinctions.
This paper proof is not yet formalized in Lean; the finite31x31 check is only
a regression check of the family, not its proof.

## Run-template calculation

For a fixed proper run skeleton and a heavy set H, replace singleton runs by
length1 and heavy runs by arbitrary lengths>=2. Solvability depends only on
this template, by the existing run-state semantics. With r runs and h heavy
runs its ordinary generating function is

    z^(r+h)/(1-z)^h.

Summing this over winning templates gives W(z), counting distinct words once
because maximal runs are unique. This is a valid exact identity, but it does
not solve enumeration: the winning-template distribution remains unknown.
The computation uses a direct normalized-run solver and independently compares
it with raw maximal-run search for every tested template through7 runs. Its
weighted sum agrees with all independently enumerated ternary words through9.
The maximum minimal-heavy-set counts for r=1..9 are1,1,1,2,2,5,5,12,12;
these nine values are not used to claim a general recurrence.

## Initial exhaustive kernel census

All crossing two-class patterns of each stated profile, modulo swapping equal
size classes, were included:

| Profile | Patterns | Coefficient histogram | Full-join zeros |
|---|---:|---|---:|
| (5,6) |451|0:429; -1:22|44|
| (5,7) |780|0:732; -1:12; 2:36|72|
| (6,6) |456|0:426; -1:30|53|
| (5,8) |1,274|0:1,183; 2:65; 6:26|117|

Every full-join case was also evaluated by signed joins on original position
partitions. Every(5,6) case agrees with the earlier independent raw-game
Möbius census. These numerical totals overlap prior work; their new use here is
the explicit separator-collapse mechanism and the tests of proposed summaries.

The first holdout exhausts crossing(6,7) and(7,7) patterns and uses fixed-seed
samples of300 each for(5,5,6),(5,6,7), and100 for(8,8). It records808 cases with
full generator join, including443 zeros that collapse by vertex domination
and16 additional zeros where elementary collapses finish the proof. Random
sampling produced only one full-join case in each three-class profile, so it
would be misleading to claim substantial three-class coverage from this batch.

The16 residual cores have zero reduced homology over F2, but that alone would
not prove contractibility. The actual elementary-collapse traces, separately
checked for unique cofaces, supply the stronger finite result.

## Most useful next conjecture, and its limits

For raw-crossing-connected patterns with at least two classes, every class
size>=5, and full generator join, investigate:

    original coefficient zero  =>  separator complex collapses to a point.

This is a CONJECTURE. The reverse implication is covered by the proved Euler
bridge and the new collapse theorem. A general constructive proof could replace
large signed cancellations by local operations. It would still leave the
classification and enumeration of surviving cores to solve.

Do not assume homology is always concentrated in one degree. The one-class
six-point control has reduced F2 Betti numbers beta0=3,beta1=2, giving the
coefficient-1 by cancellation; the one-class eight-point control also has two
nonzero degrees. Connected multi-class observations cannot be generalized to
all complexes or turned into a homotopy theorem from Euler data alone.

## Reproduction and failures

Run `analytic.py`, `language.py`, `topology.py`, `holdout.py`, `decision.py`, then
`replay.py` in this directory (from the repository root or using absolute paths).
The analytic solver uses exact Fractions, not floating-point numerical fitting.
The replayer imports none of the search helpers: it builds local catalogues by
unrestricted set partitions followed by a noncrossing filter, and verifies
all domination and unique-coface conditions independently.

Preserved unsuccessful attempts include missing SymPy in both Python runtimes,
an incorrect expectation that the first prime-factorization collision would be
at length6 (it is length5), and a Lean simplification failure on the singleton
powerset sum. The successful proof explicitly uses the powerset sign-sum lemma.
An initial full build failed on that last line; its subsequent audit still saw
the OLD compiled root. That old audit is retained as such and is not the final
proof audit. A new fail-fast full build and audit were then run.

The larger adversarial follow-up (`deep_holdout.py`) is distinct from the first
holdout and must be reported with its actual completion/skip status. It is not
silently added to any of the totals above.

## Deeper adversarial follow-up

The completed bounded follow-up tries1,973 distinct patterns, of which1,879
have full generator join. It evaluates1,847 and explicitly skips32 exceeding
the400-generator budget. The evaluated set includes1,800 inflated(5,5,6)
patterns:1,576 zero and224 coefficient-1. Across this batch all1,592 evaluated
zero cases collapse; no universal theorem follows from this selected family.
The first unbounded attempt was interrupted before producing results; its source
and empty output log are preserved. Added resource limits are visible in code.

The stronger homology-purity conjecture is KILLED even for crossing-connected
two-class patterns. Pattern0001001111110111, profile(6,10), has58 generators and
reduced F2 Betti numbers beta1=4,beta2=5, hence coefficient4-5=-1. The data also
contains a(9,9) survivor with nonzero homology in two degrees. Therefore a
classification must retain cancellation between dimensions, not just count
spheres of one fixed dimension. The targeted homology_search.py tests the
remaining collapse conjecture near the(6,10) witness; see its actual result.

Final local source verification:232 active modules,3,927 audited declarations,
only propext/Classical.choice/Quot.sound; both negative verification guards pass.
New hosted CI is tracked in receipts.json. Local proof status remains separate
from hosted certification until that exact source run succeeds.

Targeted follow-up outcome: all360 positive six-run compositions of(6,10) were
examined.201 have a proper generator join; the remaining159 were evaluated
without budget skips.57 have coefficient zero, all with zero reduced F2
homology. No counterexample to collapsibility was found by this necessary-condition
test; vanishing homology does not itself certify a collapse.

Across the three trace batches there are2,337 zero-case checks, representing
2,336 distinct original patterns. Every trace is independently replayed. The
initial+holdout+deep structural replay covers286+808+1,847 instances, respectively.
All large result JSON files and failed/passing logs are preserved in
`evidence.tar.gz`; extract it at the repository root to restore their paths.
`evidence_manifest.json` records SHA256 digests. Re-running the scripts regenerates
the results, so the archive is not a prerequisite for the exact CI job.
