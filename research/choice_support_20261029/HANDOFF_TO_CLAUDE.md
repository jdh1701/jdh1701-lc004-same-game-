# Supported domains now handled; focus next on geometry and coefficient identity

The previous abstract quotient/core CI 40968123417 at f83b4626 is green. New
modules `ChoiceSupportedDomains` and `ChoiceSupportedCancellation` compile
locally and are imported in the root: 197 modules, 2494 audited declarations,
standard axioms only; negative guards pass. New CI state is in CI_RECEIPTS.json.

The final theorem `choiceAlternatingSum_zero_of_covered_binary_spec` handles
unused values and constant coordinates internally. Its remaining caller inputs
are a binary specification, local majority closure, cover edges crossing all
proper cuts, and at least three solutions. Its concrete three-solution example
uses ambient domains of size three with one unused value per coordinate.

Do not transport `ChoiceCoordinatesConnected` blindly through support
restriction. The new exact counterexample A={(x,x,y,y):x,y in {0,1}} on ambient
domain {0,1,2} is majority-closed and binary-determined, has a complete raw
nonuniversal graph, and has a covered equality edge. Its supported graph has
two components and its alternating sum is 1. The correct cover-through-each-cut
condition is formalized and survives normalization when coordinates vary.
Both negative controls and 38 positive stored geometric checks are retained.

Suggested next encoding to assess: retain all ten 2+3 splits of a five-class,
enforce internal noncrossing as part of pair compatibility, and let supported
normalization discard unused choices. For j>=2 this could avoid a separate
five-adjacent-choice enumeration lemma. This design has not yet been implemented
or linked to original certificates; j=1 requires separate handling.

The next formal targets are the finite geometric closure/cover properties,
order transport to original positions, and winningJoinCoefficient/face-sum
identification. The all-five game theorem remains PROVED-PAPER; full fixed-q
counting and mixed profiles remain open. No direct Claude session was contacted.
