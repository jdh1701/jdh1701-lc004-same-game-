# Actual five-class law plus a raw-compatibility SCC survivor filter

Read REPORT.md and the eight new modules imported by FiveClassSurvivorRecognition.
Local full build passes215 modules; audit3574 declarations, standard axioms only;
both negative guards pass. Exact-commit CI pins are recorded via CI_RECEIPTS.json.

The key new project-level algorithmic result is not merely another table check:
`choice_pair_rigid_iff_implication_strong` and its actual-game-geometry specialization
`fiveClass_survivor_pair_iff_strong` prove the following. Given two valid tuples
a,b differing in every class, form an arc i->j iff the raw compatibility forbids
(b_i,a_j). They are the whole solution family iff the graph is strongly connected.
It does NOT use exact projections or enumerate A first. Majority closure, binary
spec, symmetry and one covered edge are material hypotheses. The proof constructs
a third solution from a nontrivial reachable set when the graph is not strong.

Use this as a FILTER in candidate-pair enumeration. Accepted pairs cannot be
multiply counted within a pattern: the theorem certifies they are its only two
certificates. Pair generation and full counting remain separate, exponential
problems. Do not interpret this as polynomial-time counting or worldwide novelty.

New two-search/SCC program exactly recovers support5 over126 partitions atn10,
and35 over126126 partitions atn15, without enumerating the full certificate family
or expanding signed joins. It exports268 candidate cases;228 rejections have an
explicit third certificate. Sage CI independently checks the graph and enumerates
those small families. Exhaustive2619 three-variable majority-closed CSPs and330
separated geometric pairs agree; four hypothesis-removal controls reject shortcuts.

Also completed: arbitrary actual-class rank normalization, consistent split-label
transport, the real split-family binary spec, >=3 cancellation, all boundary cases,
exact pair/triple cover, and the partition-join criterion in the class/rank model.
The face sum is-1 exactly for the unique separated pair, otherwise0.

Remaining formal bridge: all ORIGINAL CertificateConstraint partitions refining
an all-five pattern must be bijected with these tuples; prove the inverse and
identify winningJoinCoefficient with the face sum. The join theorem is currently
in Fin k x Fin5 coordinates, so transfer it to the original positions explicitly.
Then prioritize counting SCC-admissible planar certificate pairs and mixed kernels.

Actual n25 run40942806037 is IN PROGRESS at reconciliation, source56d867dd...
No result accepted and no duplicate long run launched. The new filter may be useful
for its next iteration; do not rewrite a running job or silently change its method.
All new results remain locally Lean-verified pending their own exact-commit CI.
