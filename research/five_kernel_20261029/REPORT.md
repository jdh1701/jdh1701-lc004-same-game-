Status: PROVED-PAPER with complete local Lean verification, awaiting exact
new-commit CI before the PROVED-LEAN label. The full project build passes
207 active modules; the axiom audit passes 3480 declarations with only the
three standard axioms; both negative guards pass.

# Kernel-checked five-versus-five geometry

## Scope

This pass formalizes the finite local input to the all-five cancellation
argument. It does not claim the original game's all-five coefficient theorem
or solve general counting. Exact-commit CI and local outcomes are recorded
in CI_RECEIPTS.json after verification; its follow-up pointer records exact
commit/run IDs without retriggering a build of unchanged proof source.

The inventory comprises all 252 sorted five-element subsets of ten ranks;
the other class is the complement. All ten choices of a pair in each five-class
are included, with the remaining three points forming its triple. Internal
noncrossing is enforced by requiring the four resulting blocks to be a
noncrossing block family. This intentionally permits unsupported ambient choices.

## Formal statements

`FiveClassFiniteGeometry.lean` proves that its executable endpoint-pair crossing
predicate is exactly `BlocksCross`, and that its Boolean family check is exactly
`NoncrossingBlockFamily`. Increasing endpoint pairs are enumerated before checking
alternation, avoiding unnecessary endpoint quadruples. Generic closure lemmas
cover rectangles, intersections, row/column fans, and arbitrary two-point
relations. Two-point closure does not require the points to differ in both
coordinates.

Six generated case modules supply all 252 concrete relation identities.
Their shapes are 120 rectangles, 102 empty relations, 20 restricted fans,
and 10 two-point relations. The generator's shape witnesses and input JSON
are untrusted suggestions: Lean independently reduces each relation's 100
entries using the geometric definitions and checks the suggested identity.
The generic `finiteRelationMatches_sound` theorem turns the Boolean table
certificate into the universally quantified relation identity.

`FiveClassGeometryExhaustive.lean` checks inventory coverage against
`(List.range 10).sublistsLen 5`, rather than assuming that the Python list is
complete. Its main theorem `fiveClass_finite_geometry` asserts local majority
closure and a row/column cover whenever the original classes cross. Empty
relations satisfy the cover condition vacuously.

`FiveClassGeometryApplication.lean` transfers these two obligations to the
four split blocks placed by any strictly increasing map of the natural rank
line. This states the placement map explicitly; it does not yet construct
such a normal form from arbitrary game color classes.

## Provenance and checks

The earlier Python computation was exhaustive on this finite domain and used
an independent endpoint implementation. It supplied candidate relation shapes;
it is not itself a formal premise. All generated computational proofs use
`decide +kernel`, not native evaluation or a new axiom. No heartbeat or recursion
limit is increased. Sequential elaboration and a chain of module imports bound
build concurrency. The generator supports `--check` to reject stale generated
source in CI. Failed attempts and diagnostics are retained.

The exact job still reruns the Python geometry check, as well as checking that
its shape witnesses reproduce the committed Lean source. A kernel-checked
theorem is stronger than this replay and does not depend on Python correctness.

## Remaining work toward the game coefficient theorem

1. Construct the pairwise rank normal forms from actual disjoint five-element
   color classes and align the ten split labels across all class pairs.
2. Prove that the actual certificate family is exactly the resulting binary
   solution family; derive the cover cut condition from NC connectedness.
3. Identify the game's join coefficient with the alternating face sum and
   assemble the empty, one-, two-, and at-least-three-certificate cases.

Surviving-pair enumeration and mixed-profile connected coefficients remain
further mathematical tasks for the full counting problem. No new coefficient,
n25 result, novelty claim, completion percentage, or time estimate is asserted.

## Claude reconciliation

Reviewed PR36 at 6cc82bcca69bb956156e1604a4bd9b4c4d1961bb. Claude independently
recomputed the ten-split closure and covers with a different crossing test:
252 arrangements, 242 crossing, 140 nonempty crossing, zero failures. Its three
review artifacts are copied unchanged under the earlier geometry folder and
its script was replayed locally. Claude's note retains an important correction:
a row-count shortcut on the ambient ten-choice domains produced 70 false flags;
unsupported values invalidate that shortcut. The discarded first script was not
present in the PR, so only the author's explanation of that failed attempt is
available. This does not change the finite theorem being checked here.

Scope correction to the older 3600-trial review: the supplied
`verify_general_abstract.py` forces a full two-fan on one edge of a random path,
and allows universal edges elsewhere. It does not explicitly test or filter
cut-connectivity; some such universal edges disconnect the exact constraint
graph. It also does not force the size-two matching boundary case. Therefore
its zero failures are supportive data for that generated family, not 3600
verified instances satisfying every hypothesis of the general theorem, nor
independent verification of the connectedness assumption. This limitation does
not challenge the separately kernel-checked theorem.

Previous rank-transport proof commit 2d8f0e78a4407f491681eda7dae2fcd54af839b9
now has green CI40977784940; probes40977784898 also succeeded. Its status is
PROVED-LEAN, while this pass's new source awaits its own exact-commit CI.

## Failed attempts and implementation corrections

The retained attempts include a missing executable decision instance for the
original crossing predicate, list-product notation mismatches in the faster
checker proof, generated tactic indentation and final empty-list disjunction
errors, a fan lemma whose six arguments were initially ordered differently
from ChoiceRelationClosed, and the final inventory disjunction associativity
fix. Two checks were stopped after resource use grew; their partial logs are
retained. The final Boolean certificate and sequential build do not change
any mathematical hypotheses. Failed-compile logs may mention sorryAx in
unresolved declarations; final source acceptance is determined by the full
build, project-wide audit and both negative guards, not by those failed logs.
