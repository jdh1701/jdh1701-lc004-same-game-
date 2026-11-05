# Support restriction and geometric cover criterion, 2026-10-29

The new cancellation theorem handles unused ambient values and constant
coordinates internally. This closes the supported-domain restriction gap in
the abstract proof. The original five-class geometry and coefficient identity
still need their Lean bridges; the full all-five game theorem remains
PROVED-PAPER and the full counting problem remains open.

The final local build passes **197 modules**. The project-wide axiom audit
passes **2494 declarations**, permitting only `propext`, `Classical.choice`,
and `Quot.sound`; both negative guards pass. New exact-commit CI is tracked
in `CI_RECEIPTS.json`. New theorems are PROVED-PAPER with local Lean
verification until that run is green. The previous complete abstract core is
PROVED-LEAN at `f83b4626f7b4be4b0098d8330b5199fabfd49863`, CI **40968123417**
success; its broader coefficient checks **40968123431** also succeeded.

## New Lean results

`ChoiceSupportedDomains.lean` constructs the supported domain at coordinate i
as the subtype of values appearing in a solution. It proves:

* The supported solution family has exactly the same number of solutions.
* Its pair projections agree with the original projections on supported values.
* Binary determination and conservative-majority closure are preserved.
* Nonconstant coordinates give nonsingleton supported domains.
* The support embedding preserves the alternating face sum.

`ChoiceSupportedCancellation.lean` proves the appropriate connectedness
criterion and assembles `choiceAlternatingSum_zero_of_covered_binary_spec`.
For at least two coordinates, this final theorem requires only:

1. A finite solution family A specified exactly by binary constraints C.
2. Local conservative-majority closure of C.
3. Every proper nonempty cut is crossed by a constraint whose allowed pairs
   lie in the union of one row and one column.
4. At least three solutions.

The alternating face sum is then zero. No full-support, nonconstant-coordinate,
global-closure, binary-determination, or quotient assumption is left for the
caller to assert separately. A constant coordinate gives a cone. Otherwise
the proof normalizes to supported nonsingleton domains and uses the previous
complete abstract cancellation theorem.

`ambientThreeChoiceFan_cancellation` supplies a kernel-checked example with
three solutions on two ambient three-value domains, where value 2 is unused
in both coordinates. It exercises the actual normalization branch. Its
cardinality and absence of value 2 are also checked in Lean. There is no
native evaluation or additional axiom.

## A rejected shortcut and the corrected criterion

KILLED candidate lemma: restricting a solution family to supported values
preserves connectedness of its nonuniversal exact-pair relations without
additional hypotheses.

The stronger counterexample is

    A = {(x,x,y,y) : x,y in {0,1}}, with ambient domain {0,1,2}.

There are four solutions. Every coordinate varies; A is majority-closed and
binary-determined. Before restriction, every pair relation is nonuniversal
because value 2 never occurs, so the apparent constraint graph is complete.
After restriction, only the equality edges (0,1) and (2,3) are nonuniversal;
the graph is disconnected. Its alternating face sum is **1**, verified both
by direct enumeration of faces and by the projection formula. It even has a
covered equality edge, so reusing the old connectedness after normalization
would invalidate the cancellation argument. The earlier theorem's full-support
hypothesis is material and is respected by its new application.

The correct criterion tracks covers across every proper cut. If a cut is
crossed by an edge satisfying `a_i=p or a_j=q`, and neither coordinate is
constant, there is a supported value different from p and another different
from q. Their pair cannot occur. Thus that edge remains nonuniversal after
normalization. The pivots themselves must be supported too: an unsupported
row pivot would force the column coordinate constant, and conversely.
These facts are all proved in Lean.

## Finite controls and scope

`normalization_controls.py` independently computes pair relations, cover
graphs, majority closure, binary determination, and alternating sums for two
explicit counterexamples. Both sums are 1. It also checks the new cover-graph
condition on the 38 stored nonconstant geometric examples; all are connected.
The workflow's exact job now runs this script.

Status: VERIFIED-COMP for these explicit finite inputs, with new CI pending
at initial upload. The 38 examples come from the earlier biased sample and
are not an exhaustive large-n verification. No new coefficient or n=25 count
is asserted. Actual n=25 run 40942806037 remains queued at reconciliation.

## Next concrete game bridge

The caller now needs the finite local geometry to provide just two properties:
local majority closure and row/column-cover edges crossing every proper cut.
A complete taxonomy of relation shapes need not be exposed to downstream
proofs. For the all-five model, crossing-class compatibility should supply
the cover edges; NC connectedness supplies a crossing edge through every cut.

Candidate encoding to test: use **all ten** pair/triple splits of each
five-class, rather than only the five internally noncrossing splits. Include
internal noncrossing in the binary compatibility predicate. For at least two
classes, every coordinate participates in a pair constraint, so internal
validity can be enforced there. Unsupported choices are now handled by the
normalization theorem. This could avoid first proving a cyclic-adjacent-pair
enumeration lemma. It is an implementation proposal, not an implemented
game representation or a completed geometry theorem; the one-class case
must remain separate.

After that representation is verified, formalize the finite local properties
and their order-preserving transport to the original positions, then identify
`winningJoinCoefficient` with the face sum and handle the two-certificate
case. Enumeration of surviving pairs and mixed-profile connected kernels
remain further mathematical tasks.

## Reproducibility and failures

All source is in the root import closure. `support-attempt-1.log` and the
successive `cancellation-attempt-*.log` retain failures involving supported
subtype finiteness, equality-instance coherence, and an expensive attempted
conversion that exceeded the default heartbeat limit. The final proof uses
explicit equality-decision invariance and instance arguments; it compiles
within the normal limits. Those transports express independence from the
choice of equality decision procedure, not a change to the solution family.

Compiler failure logs can contain placeholder `sorryAx` entries; the final
source and project audit accept no such dependencies. Final passing logs are
`full-build.log`, `coverage.log`, `axiom-audit.log`, and `guards.log`.

```
lake build LC004
python scripts/check_lean_coverage.py
lake env lean scripts/AxiomAudit.lean
python scripts/test_verification_guards.py
python research/choice_support_20261029/normalization_controls.py
```
