# Formal cancellation core, 2026-10-29

The reduced-system cancellation theorem and the coordinate-deletion invariant
now compile in Lean, together with the relation classification and universal
replacement argument. The full local build passes **190 active modules**;
the axiom audit passes **2382 project declarations**, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Both negative verification guards pass.

The whole all-five game theorem remains **PROVED-PAPER**, not PROVED-LEAN.
New exact-head CI is requested by this commit; until it passes, the new results
are recorded as paper theorems with local Lean verification. The previous
four supporting lemmas are already PROVED-LEAN at commit
`895dcec1830fc5f710c5db63d786690ca345c428`, run **40952508624**.

## Precisely what was formalized

| File / main theorem | Mathematical content |
|---|---|
| `ChoiceRelationClassification.lean`: `choiceRelation_classification` | A majority-closed binary relation with full support on nonsingleton domains is universal, bijective, or a two-fan. This is unbounded, not a finite check. |
| Same: `choiceRelation_bijective_of_isolated_pair` | A mutually forcing pair of values forces a bijection of the full supported domains. |
| `ChoiceUniversalValue.lean`: `choice_exists_universal_value` | After excluding bijective coordinate pairs, a largest solution fiber supplies a value compatible with every value in every other coordinate. |
| Same: `choice_universal_value_replace` | In a binary-determined solution family, replacing the chosen coordinate by that value preserves membership. |
| Same: `choiceBinaryDetermined_of_binary_constraints` | A family specified by binary constraints satisfies the binary-determination hypothesis; it is not silently assumed for arbitrary tuples. |
| `ChoiceReducedCancellation.lean`: `choiceAlternatingSum_zero_of_reduced_system` | The alternating face sum is zero for a supported, majority-closed, binary-determined finite system with no bijective coordinate pairs and a nonuniversal neighbor for every coordinate. |
| Same: `binaryChoiceFan_alternatingSum_zero` | A three-solution two-fan satisfies all the hypotheses simultaneously. Its hypotheses are checked by kernel `decide`, without native evaluation. |
| `ChoiceFunctionalElimination.lean`: `choiceAlternatingSum_delete_bijective_coordinate` | Deleting a coordinate bijectively linked to a retained coordinate preserves the alternating face sum. |

There are also supporting lemmas for projections, fibers, cones, and simultaneous
dominated-vertex deletion. They are in the root build closure. The general
deletion lemma only requires each value of the deleted coordinate to force
a value in the retained coordinate. It preserves the face sum, **not necessarily
the number of solutions**. The bijective corollary is the one used in the paper.

## Simpler proof of the universal-value step

For each coordinate-value pair (i,x), let F(i,x) be its set of supporting
solutions. Choose one with maximal cardinality. If it forces (j,y), then
F(i,x) is contained in F(j,y); maximality makes those finite sets equal.
The values mutually force each other, so the relation-classification lemma
makes coordinates i and j bijectively linked. Once those links have been
eliminated this is impossible. Every other row is therefore universal.

This replaces the directed-graph acyclicity argument without changing the
theorem. It removes a graph formalization obligation and uses only finite
subset/cardinality reasoning already available in mathlib.

## Remaining end-to-end obligations

1. Construct the quotient by bijectively linked coordinates on supported
   domains. Prove that the projected solution family keeps its binary
   description and has no isolated nonuniversal coordinate when more than
   one quotient coordinate remains. The face-sum deletion invariant is now
   available, but it alone does not establish these structural facts.
2. Handle the one-component/two-solution case and transport the reduced
   complex through its vertex relabeling. Constant-coordinate and empty cases
   must also be included in the final assembly.
3. Connect the original five-class certificate definitions to the explicit
   local table, majority closure, and binary constraints; formalize the
   incidence/projection/face-sum identification with `winningJoinCoefficient`.
4. Assemble the complete all-five statement, then pursue enumeration of the
   surviving pairs. The general mixed-profile connected kernel remains open.

These are proof obligations, not an estimate of the number of turns remaining.
No closed form for fixed q >= 3 or new n=25 count is asserted.

## Baseline and independent evidence

`BASELINE_CI.json` records successful run 40952508624 on 895dcec1: Lean job
123724019280, exact job 123724019186, and Sage job 123724018890 all passed.
Sage 10.10 independently checked Euler characteristic 1 and zero reduced
rational homology for all 38 stored geometric examples, and passed the
two-component control. Broader coefficient run 40952508600 also succeeded.

Claude's branch advanced to `d0efa2b6317617fdd1a2384a1a2d396053dfa052`.
`CLAUDE_REVIEW_SNAPSHOT.md` is its review of the older GPT commit fd64c4d:
2000 independent abstract projection checks and all 45 pairs of five-set
pair/triple splits passed. This is independent confirmation of the projection
identity, **not a review of the later universal cancellation argument**.
Claude's actual n=25 run 40942806037 was still queued at this reconciliation.

The earlier OpenAlex failures remain recorded; no new novelty inference was
made. This pass concentrated on the missing formal arguments rather than
repeating the literature search or generating more random cancellation tables.

## Failure record and reproducibility

Every retained `*-attempt-*.log` reports the successive local elaboration
results. The failures were: negated-equality field notation; an explicit
nonempty sigma-type witness; an argument-order mismatch; classical versus
explicit decidable-equality instances at a noncomputable image; and missing
unfolding of finite predicates/unique existence in the nonvacuity check.
Dedicated membership lemmas and explicit finite witnesses resolved them.
No failed version was promoted to PROVED-LEAN. Compiler error logs can contain
`sorryAx` for failed elaboration placeholders; the final source guard and
project-wide axiom audit reject such dependencies in accepted declarations.

`full-build-failed-1.log` and `full-build-failed-2.log` preserve two aborted
full-build attempts caused by the unfinished finite example. The final
`full-build.log`, `coverage.log`, `axiom-audit.log`, and `guards.log` pass.
On a normal Lean installation, reproduce with:

```
lake build LC004
python scripts/check_lean_coverage.py
lake env lean scripts/AxiomAudit.lean
python scripts/test_verification_guards.py
```

The local loader shim is an environment workaround for executable discovery;
GitHub CI uses the ordinary pinned Lean 4.19.0 toolchain. The CI workflow now
also triggers on Lean source/import changes so these additions cannot miss
the full build and axiom audit.


Follow-up: exact proof-commit CI 40963222453 at 1ff8e2c69979c75bdd5a67437151abf7df34e433 is now successful. The reduced-system results have green CI. Further global quotient/boundary assembly is documented in `../choice_reduction_20261029/REPORT.md`; its new exact-commit CI is tracked separately.
