# Five-class finite geometry bridge

The full counting problem remains OPEN. The abstract support-normalized cancellation
theorem is now PROVED-LEAN at c799420d1412535d3a56e8061882a6f6770182eb,
CI 40973071008 success; coefficient probe CI 40973070990 also succeeded.
This pass advances its game-specific input without claiming that input is finished.

## Exact finite check

VERIFIED-COMP, pending exact-commit CI: `ten_split_check.py` enumerates all
252 labelled five-versus-five interleavings of ten positions. It uses all ten
pair/triple choices per class, including the internally crossing choices, and
requires every pair of the resulting four blocks to be noncrossing. Crossing is
implemented directly through alternating endpoints, independently of the
previous run-count implementation in `core.py`.

All 252 compatibility relations are closed under the conservative majority
operation. Of these, 242 have crossing original classes; each is covered by one
row and one column. 140 crossing relations are nonempty; empty relations satisfy
the cover property vacuously. All 175980 triples of allowed pairs were checked.
Each individual five-point class has exactly five internally noncrossing choices.
No quotient by symmetry, sampling, or novelty inference is used.

This validates the proposed ten-choice encoding at the finite computational
level. It has NOT yet been encoded and proved exhaustively in Lean.

## Formal bridge lemmas

PROVED-PAPER with local Lean verification, pending exact-commit CI:
`LC004/FiveClassGeometryBridge.lean` proves:

* Crossing of two blocks is invariant under strictly increasing maps.
* A whole block family is noncrossing iff its increasing image is noncrossing.
* More generally, two maps giving identical strict comparisons give identical
  crossing predicates, without an injectivity assumption.
* In particular, crossing of lists of finite ranks is equivalent to crossing
  of their images under any strictly increasing map to actual positions.
* On at least two coordinates, a conjunction of unary validity conditions and
  binary constraints is equivalent to binary constraints absorbing both unary
  conditions. This justifies enforcing internal split validity on each edge.

These are transport and specification lemmas, not a completed bridge from
winning game certificates to the abstract solution family. The first failed
Lean attempt is retained; its membership-variable shadowing errors were fixed.

## What remains

1. Define the finite ten-choice compatibility relation in Lean and prove its
   closure and crossing-cover properties. Use the rank transport above.
2. Assemble the actual certificate-family binary specification, crossing-cut
   connectedness, and the coefficient/face-sum identity. Handle empty, one,
   and two certificate cases to finish the all-five coefficient theorem.
3. Enumerate the surviving two-certificate structures and resolve the mixed
   block-size connected coefficients required for the full counting problem.

The first two items are bounded formalization goals with a paper argument;
the third contains unresolved mathematics. These are work areas, not a prediction
of three turns or a guaranteed finite checklist to full resolution. The current
approach remains productive because it has delivered structural Lean theorems
and eliminated false shortcuts; a full counting formula is not yet close enough
to forecast a completion date or percentage.

The workflow now includes this finite check and explicitly watches the support
and geometry research folders, so future research-only updates trigger it too.

## Verification receipt

Local full build passes 198 active modules. The axiom audit passes all 2501
project declarations, allowing only propext, Classical.choice and Quot.sound.
Both negative verification guards pass. Exact new-commit CI is recorded in
CI_RECEIPTS.json once created; this does not retroactively upgrade the finite
Python theorem to a Lean proof.
