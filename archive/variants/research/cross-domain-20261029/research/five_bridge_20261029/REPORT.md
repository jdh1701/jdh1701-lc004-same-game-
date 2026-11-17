# Original-game all-five coefficient bridge

Final status: **PROVED-LEAN**. Exact proof commit ba0357de passes CI40992099928;
verification commit c51b75ab passes Lean/exact/Sage CI40992346166 and coefficient
probes CI40992346252. See `research/FIVE_BRIDGE_CI_RECEIPTS_20261029.json` for
full commit, job, and run pins.
No global novelty claim. The general counting problem remains **CONJECTURE / OPEN**.

## Main result

Let p be an original position-equivalence pattern whose classes all have size 5.
Assume at least two classes, and that the graph joining two original classes when
their position lists cross is connected (formally, every nonempty proper cut is
crossed). Let C(p) be ALL original CertificateConstraint patterns c with c <= p.
Then the original collected join coefficient satisfies

    winningJoinCoefficient n p = -1
        exactly when C(p) = {c,d} and c join d = p;
    winningJoinCoefficient n p = 0 otherwise.

**PROVED-LEAN, CI40992346166 SUCCESS**:
`winningJoinCoefficient_five_original_law` in
`LC004/FiveOriginalCoefficientLaw.lean`. This no longer assumes a correspondence
between original generators and split tuples, nor an original coefficient/Euler
identity. Both are now proved. The connectivity hypothesis is explicit raw
crossing-cut connectivity; this pass does not claim a new equivalence between
that hypothesis and some different notion of noncrossing closure connectivity.

A second theorem, `winningJoinCoefficient_five_scc_law`, replaces enumeration of
C(p) by a valid separated pair plus strong connectivity of its forbidden-mix
implication graph. The graph uses raw pairwise compatibility. This is a
recognition criterion given a pair, not a polynomial-time counting theorem.
**PROVED-LEAN, CI40992346166 SUCCESS**, same CI receipt requirement.

## How the gap was closed

1. `FiveClassLocalRefinement`: every size-2/3 equivalence relation on five positions
   is exactly one of the ten pair/triple splits. All 3125 colorings Fin5 -> Fin5
   are checked by the Lean kernel; unused colors are allowed. No native evaluation
   axiom is used.
2. `FiveClassRefinementEquiv`: any small-class refinement of the class/rank base
   has a unique split tuple; the inverse is proved, not assumed.
3. `FivePatternCoordinates`: construct a canonical bijection from ORIGINAL
   positions to class x increasing local rank, preserve exact class sizes and
   identify the original p with the transported base equivalence relation.
4. `FiveCertificateGeneratorEquiv`: a complete duplication-free bijection from
   original CertificateConstraint generators below p to tuples whose encoded
   original position pattern is noncrossing.
5. `IncidenceFaceSum`: a general finite-poset separator identity. Given finitely
   indexed proper lower elements covering every strict refinement of p, the
   alternating sum of lower-incidence values at their meets is f(p). Specializing
   to original winning incidence gives an original coefficient/Euler identity for
   EVERY pattern, including empty/losing cases. The universal version can use all
   proper refinements and does not depend on class size five.
6. `FiveClassSeparators`: use 15 cuts per class (5 singleton/four cuts and 10
   pair/triple cuts), and prove that they cover every strict refinement. This
   avoids formalizing a complete coatom classification. A small original
   certificate lies below exactly its chosen pair/triple cut in each class; the
   singleton cuts occur in no certificate facet.
7. `FiveCoefficientChoiceBridge`: identify original coefficient with the exact
   alternating choice-complex sum, with all unused vertices removed by a proved
   embedding invariance theorem.
8. `FiveEncodedBlocks` and `FiveCoordinateGeometry`: prove that the ORIGINAL
   noncrossing predicate agrees with the actual ordered split-block family.
   Increasing local rank is derived from orderEmbOfFin; positional noncrossing
   is not asserted to be invariant under arbitrary permutations.
9. `FiveOriginalCoefficientLaw`: transport lattice joins via a Setoid order
   isomorphism, apply the already proved actual-geometry cancellation/boundary
   law, and translate the result back to original certificate patterns. Add the
   original-coefficient SCC criterion using the prior recognition theorem.

All steps above: **PROVED-LEAN, CI40992346166 SUCCESS**. Previous actual-geometry/recognition proof was **PROVED-LEAN** at
c365c2ae2922a35765f9a6b692d05e838873ebcd, CI 40984245009 SUCCESS.

## Independent finite replay

`verify_global_nc_bridge.py` constructs global noncrossing certificates recursively
by interval decomposition. It does not use the ten-split compatibility table to
construct these original generators. It compares that catalogue with independent
classwise split construction, then computes signed joins on ACTUAL board-position
equivalence relations, rather than the compressed split-label coefficient DP.

**VERIFIED-COMP (local and CI40992346166 exact job SUCCESS)**:

- All 126 n10 all-five partitions have identical original and split generators;
  all 121 raw-crossing-connected cases satisfy the coefficient law.
- The 254 n15 patterns in the saved separated-pair fixtures have identical
  generators and satisfy the law. This is NOT a new exhaustive n15 count.
- The connected test cases give 40 coefficients -1 and 335 coefficients 0.
- Global NC certificate catalogues have sizes 5, 180, 10010 at n5,n10,n15 with
  respectively 1,2,3 pair blocks and the same number of triple blocks.
- The n5 one-class exclusion control has coefficient -4, not -1 or 0.
  Thus dropping the at-least-two-classes hypothesis is **KILLED** by this example.

Saved result: `verify_global_nc_bridge.json`; raw output:
`global-nc-bridge-replay.log`. This replay is finite evidence, not the general proof.

## Verification and unsuccessful attempts

Local full root build PASS; all 225 active modules reachable; axiom audit PASS
for 3729 declarations, only propext, Classical.choice, Quot.sound. Both negative
coverage/axiom guards PASS. Source guard rejects proof placeholders, custom
axioms, native_decide, unsafe/partial project source. Final theorem's printed
axioms contain only those three standard axioms.

All attempted build logs are preserved, including failures. Failures were Lean
implementation errors rather than discovered counterexamples to the final law:
cardinality-expression coercions in refinement equivalence; dependent rewriting
of the original pattern inside its quotient-coordinate type; sum factoring and
conditional simplification in incidence; finite-list image congruence; equality
conditionals in separators; shadowed list-map membership witnesses; one incorrect
library lemma name (`sorted_finRange`, corrected to `pairwise_lt_finRange`).
Failed logs can print sorryAx for Lean's recovery after an error; final source and
the successful root axiom audit do not contain or permit it. No heartbeat increase
was needed for the new proof. No Sage run was performed locally. CI reuses the
pinned Sage image and existing independent homology/SCC checks.

## What this changes and what remains

The five-point law is now about the ORIGINAL collected counting coefficients,
not only a related abstract complex. The two original-game formal obligations
listed in the preceding handoff are discharged. The n25 agreement 6455 remains
**VERIFIED-COMP**, independently in Claude CI40942806037 and transfer CI40986874442;
it is a special all-five survivor count and is NOT A(25,5).

The general counting problem is still **CONJECTURE / OPEN**: mixed class sizes,
recurrences/formulas for all survivor families, and full connected kernel counting
remain. The most productive next mathematical target is to apply the general
separator/Euler identity to the smallest unresolved mixed profiles, derive their
actual local relations, and test whether the majority/covered-cut mechanism
survives. Do not presume the all-five proof transfers. A general recurrence for
S_j = 5,35,415,6455 would also be useful, but these four finite values alone cannot
justify one. Statistical-mechanics/biochemistry/finance analogies supplied no
proved equivalence and are not inputs to this proof.

Supplemental replay distinction: `verify_original_bridge.py` is the separate
554-case position-join replay (548 connected,47 coefficients -1,501 zero),
including random cases and a disconnected coefficient16 exclusion control.
The global NC-catalogue replay above is `verify_global_nc_bridge.py`; the two
finite checks have different scopes and neither is an exhaustive n15 count.
The final two simple original coefficient corollaries add range {-1,0} and
cancellation with at least three original generators. Final audit3729 includes
those corollaries. The initial audit3726 predates them.

Final CI confirmation: proof ba0357de and verification c51b75ab both pass all
Lean/exact/Sage and coefficient-probe workflows. Full latest job logs are saved
at root research/FIVE_BRIDGE_CI_{LEAN,EXACT,SAGE}_20261029.log; exact pins and
claim scopes in research/FIVE_BRIDGE_CI_RECEIPTS_20261029.json. Earlier pending
status snapshots in this directory are superseded by that root receipt.
