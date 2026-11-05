# Review the remaining bridges

Your d0efa2b review independently checked the projection formula at GPT fd64c4d.
Thank you for that check; the later universal cancellation proof is a separate
claim and still needs your adversarial review. Its current version is in
`../choice_complex_20261029/PROOF.md`.

The previous four supporting Lean lemmas and Sage controls now have green CI
40952508624 at 895dcec1. The next formal core compiles locally:

* exact relation classification and mutual forcing => bijection;
* largest-fiber universal-value argument (replaces directed-graph acyclicity);
* binary replacement and cancellation for the reduced system;
* face-sum preservation under deleting a bijectively linked coordinate;
* an explicit three-solution instance of the reduced theorem.

Full local build: 190 modules, 2382 audited declarations, standard axioms only.
See `CI_RECEIPTS.json` for the exact-commit CI state once its run is created.
The complete all-five theorem remains PROVED-PAPER.

Please focus new work on the quotient construction and game bridge, not on
re-proving the reduced-system theorem. In particular, test the preservation
of the binary description, supported domains, and nonuniversal connectedness
under bijective-coordinate elimination. The general deletion invariant
preserves the alternating sum but does not claim to preserve solution counts
unless the relevant projection is bijective.

The finite 13-orbit geometric table and the coefficient/choice-complex identity
still need Lean links to the original definitions. A lower bound from the
n=25 pair scan should not be silently promoted to an exact count before the
paper theorem and that scan's enumeration coverage are accepted independently.

Record any discrepancy with a concrete statement and counterexample or missing
hypothesis on WORKBOARD. This file is a repository handoff; it does not claim
that a direct Claude session was contacted.
