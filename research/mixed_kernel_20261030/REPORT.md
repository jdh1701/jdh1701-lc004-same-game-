# Original mixed (5,6) kernel: verified obstruction and local transfer

## Repository reconciliation

The active proof source is jdh1701/jdh1701-lc004-same-game-, not the older
Alexandria_Omega_New root. Checked the parent repository metadata and root tree,
all open Same Game PR heads, the latest workboard and handoff. PR35 proof source
ba0357def8d61dcbc9f92a10690927a4d568f91f is now PROVED-LEAN: hosted Lean/exact/Sage
run40992099928 SUCCESS; coefficient probes40992100056 SUCCESS. Earlier pending
statements are superseded by these exact source/run pins. The branch head used
for this new work is cc038da1a0a68a9a43b05ca2483a8a6a29f26426. It includes the
independent global NC replay and archived original bridge logs. No main merge.
New isolated branch: proof/mixed-kernel-obstructions-20261030, stacked on PR35.

## New general proofs

- coefficient_eq_of_incidence_eq_below: equality of lower incidence throughout
  one principal ideal determines the coefficient at its top.
- winningJoinCoefficient_eq_local_generators: any complete LOCAL list of
  original CertificateConstraint refinements suffices to compute the original
  coefficient. Duplicate entries are permitted by the underlying signed-list
  construction; no global board-pattern catalogue is required.
- winningJoinCoefficient_zero_of_common_refinement: for ANY class-size profile,
  the original coefficient is zero if every original certificate refines one
  common separator rho while p does not refine rho. The losing case is included.

These are reusable reductions. They are not a new general closed counting law.

## Complete local catalogues

LocalCertificateCatalogues proves that every original noncrossing 2/3 partition
on five points occurs in the displayed five-item catalogue, and every such
partition on six points occurs in the displayed eight-item catalogue.
Completeness starts from an arbitrary ColorPattern, not a sampled labeling.
Canonical least-class representatives provide bounded codes. The final kernel
checks quantify explicit bounded coordinate tuples, at most120 and720 cases,
rather than all3125 and46656 unconstrained color functions. An initial broad
function check exhausted memory (exit137); its logs are retained. No custom
axiom or native evaluation axiom is introduced.

## Explicit original-game mixed coefficient

The original word is 00100110111. Its classes are
G={0,1,3,4,7}, H={2,5,6,8,9,10}. Their sizes are5 and6, and they cross.
The two ordered restrictions are saturated under every certificate refining p.
The new catalogue theorems and a reconstruction on the actual eleven positions
prove that ALL original certificate generators are exactly these three patterns:

    A = 00122332144
    B = 00122332441
    C = 00122110333

In zero-based local catalogue labels the compatible pairs are exactly
{(2,4),(2,6),(1,0)}. They have a two-fan cover s=2 or t=0, but are not closed
under the conservative majority operation: inputs(1,0),(2,4),(2,6) yield(2,0),
which is absent. Thus coveredness alone does not extend the previous mechanism.

The join of A and B is strictly below p, as witnessed by a concrete barrier.
The joins of A with C and B with C are p, and the triple join is p. These are
actual setoid-join equalities, proved with kernel-checked paths of length three.
No individual certificate equals p. Inclusion-exclusion at p therefore gives
-2+1=-1. The main theorem winningJoinCoefficient_mixed56 is about the ORIGINAL
winningJoinCoefficient, with no assumed encoding or unverified completeness.
The original generator finset has cardinality3. The existential theorem
three_generator_cancellation_fails_for_mixed_profiles refutes extending the
all-five >=3 cancellation rule unchanged to general heavy profiles.

This example was previously observed computationally. The progress here is its
complete original-game Lean proof and reusable transfer/catalogue machinery,
not discovery of the example or a worldwide novelty claim.

## Independent finite discrimination

probe.py exhausts all462 position patterns with classes of sizes5 and6. It
compares every local catalogue construction with a global recursive catalogue
of495 original noncrossing 2/3 partitions of eleven positions, and calculates
signed joins on actual position partitions. All462 generator comparisons pass.
All451 crossing-pattern coefficients also agree pointwise with the older
independent maximal-run/Mobius results56.json:429 zero and22 at-1.

Among the22 nonzero crossing cases every compatibility relation has3 entries,
is covered and fails majority closure. The other shapes include examples
where coveredness fails as well. This finite census does not prove a general
mixed-profile cancellation theorem, nor a fixed-alphabet counting formula.

## Verification and next target

The full local root build succeeds, including the five new modules. Exact
module/declaration counts, allowed axioms and guard results are retained in
final verification logs. New hosted status must be pinned to the exact proof
commit before labelling this addition PROVED-LEAN. Until then: PROVED-PAPER
with local Lean verification. Ordinary finite computations: VERIFIED-COMP.

Next useful positive target: classify all two-class(5,6) compatibility relations
up to row/column permutations, prove the surviving three-edge shape criterion
from arbitrary disjoint ordered classes, and transport that classification to
original coefficients. The sample does not justify extending all-five majority
closure, nor fitting a recurrence from the four survivor values. Mixed larger
classes and general survivor enumeration remain open. A035617 remains open.

## Discriminating follow-up: proper joins versus real cancellation

The general common-refinement obstruction explains385 of the429 zero-coefficient
crossing(5,6) cases in the finite census: the join of every original generator
is still a proper refinement of p. The remaining44 zero cases DO have full
generator join. Thus the converse, full generator join implies nonzero
coefficient, is KILLED by explicit saved examples. The remaining work cannot
be replaced by a support/connectivity test alone. The44 genuine-cancellation
cases have7,12 or16 generators; the22 nonzero cases have3.
Reproducible script: support_probe.py; results: support_probe.json.
These385+44+22 cases exhaust the451 crossing inputs of this finite profile.

## Six-point separating complex: positive reusable extension

SixClassSeparatorFacets proves a complete separating family of31 nontrivial
unordered two-part cuts of six positions. All8 original noncrossing2/3
certificates are accounted for. A two-triple certificate lies below exactly1
cut; a three-pair certificate lies below exactly3. Thus local facets are
singletons or triangles, not uniformly single choice vertices.
The actual local complex has face counts1,12,15,5 in sizes0,1,2,3; its alternating
sum is1-12+15-5=-1. Through the general original-game separator identity,
winningJoinCoefficient_single_six proves the ORIGINAL coefficient at the one-class
six-point pattern is-1. A recalled tentative value-4 was rejected by Lean and
by independent original-partition joins; the failed attempt is retained.
No incorrect value was used by the successful mixed witness proof.
The local cut-cardinality and original-coefficient proofs provide a positive
foundation for a future mixed-profile complex with correct local incidence.
Independent replay: six_facets_probe.py/json, with both bit-mask faces and
actual position-partition signed joins.
