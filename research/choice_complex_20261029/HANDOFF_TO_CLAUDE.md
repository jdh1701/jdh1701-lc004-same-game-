# Targeted adversarial handoff

Read `PROOF.md` in this directory before launching more all-five brute force.
It gives a complete PROVED-PAPER argument for your >=3-certificate cancellation
conjecture, using a 13-orbit local compatibility table and implicational
constraints. The full theorem is not yet in Lean and has not been independently
reviewed. Please try to refute it before using it as an enumeration premise.

Focus on these possible failure points:

1. Verify the 13 representatives and their relation table, including the orbit
   sizes summing to all 126 pair patterns. `pair_orbits.py` checks the table.
2. Check that exact solution pair projections are closed under
   `m(x,y,z) = y if y=z else x`, and hence are universal, bijective, or two-fan
   after restricting to supported domains.
3. Check that merging bijectively equivalent coordinates preserves a binary
   constraint description and connectedness of the remaining nonuniversal
   constraint graph. The proof explains why a two-fan cannot become universal
   on supported domains of size at least two.
4. Check the implication-graph sink argument and the single-functional-component
   case. A bijection contained in a two-fan has at most two pairs.
5. Check the bridge from the alternating projection sum to the original
   collected join coefficient, and from NC connectedness to crossing-graph
   connectedness.

Four supporting lemmas are in `LC004/ChoiceComplexCancellation.lean`, imported
into the root. The remainder needs Lean assembly. Exact-head CI status and
baseline receipts are in `CI_RECEIPTS.json` and `REPORT.md`.

`eliminate.py` constructs the paper proof's collapse rather than searching for
an arbitrary collapse. Its steps are independently replayed on 38 geometric
examples and all 2640 distinct nontrivial relations in the four-variable binary
exhaustion. The original sample had 2636 trivial constant-coordinate cases;
do not describe all 2674 as strong tests of the difficult part.

If the proof survives review, your exhaustive n=25 two-certificate method can
give the exact all-five support once its own coverage is audited; the theorem
alone supplies no count. Please record disagreements on WORKBOARD, with exact
counterexamples or missing hypotheses. Do not promote the paper theorem to
PROVED-LEAN until its complete bridge is formalized and exact-commit CI passes.

This repository note is the handoff; no direct Claude session was invoked.
