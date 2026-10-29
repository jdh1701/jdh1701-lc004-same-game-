# Global coordinate reduction and abstract cancellation, 2026-10-29

The complete abstract cancellation theorem now compiles in Lean, including
the previously missing quotient, connectedness preservation, face-sum transport,
and the one-component boundary argument. The all-five game statement remains
PROVED-PAPER: its finite geometric and original-coefficient bridges are not yet
assembled. The general fixed-q counting problem remains open.

New results are PROVED-PAPER with local Lean verification until exact-commit CI
passes. The prior reduced-system core is PROVED-LEAN at commit
`1ff8e2c69979c75bdd5a67437151abf7df34e433`, run **40963222453**, now successful.
Final local build, coverage, audit and negative-guard receipts are in this folder.

## What the new theorem actually says

`choiceAlternatingSum_zero_of_local_constraints` in
`LC004/ChoiceAbstractCancellation.lean` takes a finite solution family A and
its binary constraint description C. Assume:

1. Every value in every coordinate domain occurs in a solution, and each
   coordinate domain has at least two values.
2. Each binary constraint preserves the conservative majority operation.
3. The nonuniversal raw constraints connect all coordinates (expressed by
   crossing every proper nonempty cut).
4. There are at least three solutions.
5. One constraint lies in the union of one row and one column.

Then the alternating sum of the choice-complex faces, including the empty
face, is zero. Two-fans satisfy condition 5. A matching with at most two
pairs does too: cover one pair by its row and the other by its column.
The finite five-class compatibility classification must still establish
these geometric inputs for the original certificates.

Global majority closure, binary determination, absence of bijections after
reduction, and connectedness of the quotient are derived inside the proof.
They are not additional conclusions assumed as hypotheses. A concrete
three-solution binary fan instantiates the theorem, including connectedness
and the covered-edge condition. Its finite support and binary checks use
kernel `decide`; there is no native evaluation or additional axiom.

## The reduction bridge

| Module | Main result |
|---|---|
| `ChoiceCoordinateReduction` | A coherent surjective coordinate reduction preserves supported values, binary determination, majority closure, and connectedness. |
| `ChoiceBijectiveQuotient` | Bijectively linked coordinates form a setoid. The chosen representatives and domain equivalences give an actual quotient family with the same number of solutions and no remaining bijective coordinate pairs. |
| `ChoiceQuotientFaceSum` | Simultaneous deletion of dominated vertices and an injective representative embedding preserve the alternating face sum through the quotient. |
| `ChoiceAbstractCancellation` | Three solutions plus a covered edge rule out a one-class quotient; the general cancellation theorem and constant-coordinate case follow. |

The new construction handles all bijective links at once. Connectedness is
transported by taking inverse images of cuts under the quotient map. It never
assumes that deleting a graph vertex preserves connectedness, and requires no
cut-vertex exception or graph-homomorphism injectivity assumption.

The one-component argument is explicit: if every coordinate is bijectively
linked, fixing any value fixes the whole solution. Each value fiber therefore
contains at most one solution. A covered edge puts every solution into the
union of two such fibers, so |A| <= 2. This contradicts the three-solution
hypothesis. It does not infer a size-two bound from an arbitrary abstract
bijection.

## Claude integration and review

Claude's PR #36 contributed `ChoiceBinaryClosure.lean`. Its 40-line source
was copied byte-for-byte from commit `6bf6206e6a0949b81073c671f2e6070d773bfee0`.
It matches the source at CI-tested commit
`afe821e682b654e33298fe1521a9724a625678ce`, run **40965919575**, successful.
The integrated theorem derives global majority closure and binary determination
from the local binary specification. It is now used by our final abstract theorem.

Claude's review at branch head `be71e25587d5c4966df78594cfefcb02d7c411d2`
reports independent exhaustive checks of all 252 labeled two-class geometric
interleavings and 2500 random abstract CSP trials, with no failures. The review
explicitly distinguishes these tests from a full independent derivation or
rebuild of our later proof. `CLAUDE_REVIEW_SNAPSHOT.md` preserves that scope.
We did not rerun or upgrade those reported tests to new CI claims here.

His handoff correctly warns that `ChoiceRelationBijective` alone has no
cardinality bound. Our `ChoiceSmallEdge` hypothesis and two-fiber proof address
the abstract boundary argument while keeping the finite geometric obligation
visible. His concern about connectedness under one-vertex deletion is avoided
by the global quotient/cut construction. The original handoff is preserved as
`HANDOFF_FROM_CLAUDE_SNAPSHOT.md`; these are responses to its scoped issues,
not claims that an arbitrary bijection or vertex deletion has stronger properties.

Claude's phrase that the open problem becomes pair enumeration applies to
the all-five kernel only. Mixed-profile connected weights and general fixed-q
enumeration are still unresolved. Actual n=25 run **40942806037** was queued
at reconciliation; no new count is asserted.

## Remaining work

1. Restrict actual certificate choices to supported domains; connect the
   nonconstant case to nonsingleton domains and handle the constant/empty cases.
2. Formalize the finite five-class compatibility classification and relate
   crossing-connected game patterns to the raw constraint connectedness used
   above. Derive local closure and a covered edge from that geometry.
3. Identify the original `winningJoinCoefficient` with the alternating
   projection/face sum in Lean; assemble the two-certificate and zero cases.
4. Enumerate the surviving pairs. The general mixed-profile kernel still
   requires further mathematics even after the all-five theorem is completed.

The quotient construction, its connectedness preservation, and the abstract
one-component bound are no longer listed as missing; this pass supplies them.
No new novelty claim or broad analogy search was made.

## Verification and failure record

All source is imported through `LC004.ChoiceAbstractCancellation` in the root.
Successive `*-attempt-*.log` files retain compiler failures and their fixes:
dependent-index transport, explicit quotient setoid inference, the dependent
quotient domain in reduction lemmas, membership under representative embeddings,
and consistent decidable-equality instances at the face-sum interface.
Compiler error logs may show `sorryAx` placeholders for failed elaboration;
the final source guard and axiom audit reject them in accepted declarations.

`pre-integration-*` logs preserve a passing 194-module build before integrating
Claude's closure lemma and the final local-constraint wrapper. The final
`full-build.log`, `coverage.log`, `axiom-audit.log`, and `guards.log` apply to
the integrated source. `CI_RECEIPTS.json` records the new run once created;
pending CI is not PROVED-LEAN evidence. Reproduce with the ordinary pinned
Lean/mathlib 4.19.0 commands:

```
lake build LC004
python scripts/check_lean_coverage.py
lake env lean scripts/AxiomAudit.lean
python scripts/test_verification_guards.py
```

Final local verification: **195 active modules**, **2450 audited declarations**, build/coverage/axiom audit and both negative guards pass. Standard axioms only.
