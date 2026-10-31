# Actual five-class cancellation and an SCC survivor recognizer

The new result is a project-level algorithmic advance: after finding two
noncrossing split certificates that differ in every five-point class, uniqueness
of that pair is exactly strong connectivity of a graph computed from raw local
compatibilities. It does not require enumerating the remaining certificates.
The theorem and its actual-geometry specialization are locally Lean-checked.
Exact-commit CI determines when the new PROVED-PAPER/local-Lean results are
promoted to PROVED-LEAN; see CI_RECEIPTS.json and its follow-up pin file.
No claim of worldwide mathematical novelty is made.

## The recognition theorem and proof

Let A be the exact solution family of symmetric binary constraints C, closed
under the conservative majority m(x,y,z)=y when y=z, otherwise x. Let a,b lie
in A with a_i != b_i at every coordinate. Assume one coordinate pair covers
all solutions by a_i=p OR a_j=q (ChoiceSmallEdge; pivots here are arbitrary).
Form a directed graph with an edge i -> j whenever i != j and

    NOT C(i,j,b_i,a_j).

Then

    A = {a,b}  iff  this graph is strongly connected.

`ChoiceImplicationRecognition.lean` proves both directions for general dependent
coordinate domains, not just five-class geometry. No finiteness of the index
type is needed for the mathematical characterization; the algorithm is for
finite instances.

For sufficiency, apply m(a,b,c) and m(b,a,c) to any c in A. Along an edge,
c_i=b_i forces c_j=b_j; in the opposite direction c_j=a_j forces c_i=a_i.
Strong connectivity propagates any such equality globally. The single cover
forces c to agree somewhere with a or b: its row pivot must occur in a_i or
b_i, or both a and b would have the same covered column value; similarly for
the column pivot. Thus every c is a or b.

For necessity, if j is not reachable from i, let S be the vertices reachable
from i and set c_l=b_l on S and a_l outside S. Closure of S under the graph's
arcs, symmetry of C, and validity of a,b make c a valid solution. Since i is
in S and j is outside, c differs from both a and b. This contradicts A={a,b}.
The Python implementation constructs and checks this third certificate for
every rejected candidate pair, rather than merely reporting a negative flag.

The graph uses raw compatibility C, not exact projections obtained by first
solving the entire instance. Given the pair, it takes O(k^2) local compatibility
queries and an ordinary directed-graph reachability/SCC computation. Finding
the pair can still require search. No polynomial-time general counting claim
or measured speedup factor is asserted.

All game-specific cancellation/recognition theorems assume at least two
classes (`Nontrivial (Fin k)`). The one-class case is excluded.

## Removing the actual-geometry hypotheses

The following are now proved, uniformly in the number and spacing of classes:

* `five_classes_rank_normal_form` constructs an increasing placement and the
  finite rank interleaving for any two disjoint five-element sets of positions.
* `fiveSplitBlocks_map` proves that rank labels within a class are preserved,
  independently of which other class is used for the normalization.
* `fiveClass_actual_geometry` derives majority closure and crossing covers
  for arbitrary actual five-point classes, without a supplied normal form.
* `fiveClassSplitFamily_spec` proves the equivalence between noncrossing of
  the whole chosen block family and its pairwise binary specification.
* `fiveClassSplitFamily_alternatingSum_zero` derives every abstract hypothesis
  and cancels all families with three or more solutions, assuming the original
  classes are crossing-connected.
* `fiveClassSplitFamily_alternatingSum_classification` handles every boundary
  case: the sum is -1 exactly for a two-certificate family whose tuples differ
  in every class, and zero otherwise.
* `fiveAssignmentSetoid_join_eq_base_iff` identifies that separation condition
  with the partition join merging every class in the class/rank index model.
* `fiveClassAssignmentBlocks_exactCover` and its size theorem show that each
  tuple partitions the actual class positions into pairs and triples.
* `fiveClass_survivor_pair_iff_strong` specializes the graph criterion to these
  actual noncrossing split families.

The exact-cover theorem enumerates all class positions on its right side; it
is not a claim that all original game certificates have already been placed
in bijection with this representation. That inverse representation and the
original coefficient identity remain formal obligations below.

## Computational discrimination

VERIFIED-COMP, new exact-commit CI pending:

`verify_implication.py` exhausts all 14 majority-closed relations on a three-value
domain containing (0,0),(1,1), and every three-variable complete constraint
network formed from them that has at least one covered edge: 2619 systems,
459 rigid, zero discrepancies. It also checks 330 separated candidate pairs
across the crossing two-class geometry; 10 labelled cases are rigid (five
unlabelled patterns). Four hypothesis-removal controls refute dropping the
cover, majority closure, binary specification, or coordinatewise separation.
These are actual negative controls, not evidence for an unrestricted SCC rule.

`count_by_implication.py` enumerates each unlabelled five-class partition once
by putting the smallest remaining position in the next class. It finds a first
certificate, searches for one differing at every coordinate, and applies the
SCC test. It never materializes the full solution family or a signed join sum.

| Positions | Classes | Partitions checked | Candidate pairs found | Survivors |
| --- | --- | --- | --- | --- |
| 10 | 2 | 126 | 14 | 5 |
| 15 | 3 | 126126 | 254 | 35 |

These independently recompute known small survivor counts, not new n20 or n25
values. On the n15 pass the program attempts 1242848 search values; this is
not a controlled timing comparison with the previous optimized implementation.
The two searches may still have exponential worst-case cost.

All 268 candidate cases are exported. For the 228 rejected pairs the code
constructs a third valid certificate from a reachable set. `scc_check.sage`
independently uses Sage's directed-graph implementation and enumerates each
small candidate's full family to check both positive uniqueness and the third
witnesses. It is wired into pinned Sage CI; no local Sage pass is claimed.

## What remains for the original problem

1. Establish the bijection between all original pair/triple certificate
   partitions refining an all-five color pattern and this split family. The
   local arithmetic is 2r+3s=5 forcing one pair and one triple, but the partition
   and label maps, injectivity, and inverse need their formal proofs.
2. Identify `winningJoinCoefficient` with the signed face sum in that exact
   representation. The existing paper argument is not substituted for this
   Lean theorem. The partition join above is currently in the class/rank model.
3. Use the new SCC filter when enumerating candidate pairs, seeking a structural
   recurrence or generating function for accepted systems. Pattern/candidate
   enumeration is still exponential and no full counting formula is obtained.
4. Mixed block-size connected kernels remain open; majority closure and a
   small edge must not be assumed for those profiles.

The full all-five original-game coefficient statement therefore remains
PROVED-PAPER. General fixed-q SameGame counting remains OPEN. The advance here
is the complete actual split-family law and a useful recognition algorithm,
not a declaration that the open counting problem is resolved.

## Reproducibility and failures

The folder retains every completed failed Lean attempt, the final successful
module builds, full project build, coverage, axiom audit and negative guards.
An initial recognition build ended without producing an olean or final receipt;
the repeated build completed and is the accepted result. Failure logs containing
sorryAx are diagnostic artifacts; the final source audit permits no such axiom.
Several equality-instance mismatches were resolved by making decision procedures
explicit and proving their irrelevance, without increasing heartbeat limits.
Finite join-path checks use kernel evaluation, never native evaluation.

The earlier finite geometry proof at 9f53675350823a9b5a4770600e7b1b8efd083ad7
is now PROVED-LEAN: CI40980791072 success, probes40980790895 success.

## Final local verification

Full build:215 modules. Axiom audit:3574 declarations, only propext,
Classical.choice and Quot.sound. Both negative guards pass. The Python
exhaustions and independent counting program pass. Sage verification is
configured in CI and is not claimed locally.
