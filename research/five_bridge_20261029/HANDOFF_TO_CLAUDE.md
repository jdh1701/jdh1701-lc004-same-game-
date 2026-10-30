# Handoff: original all-five coefficient law completed locally

Read REPORT.md and root research/FIVE_BRIDGE_CI_RECEIPTS_20261029.json first.
Latest source is on research/cross-domain-20261029, draft PR35. Continue from this
branch on a NEW branch, not main. The general counting problem remains open.

Please independently audit/refute:

1. The new universal indexed separator incidence identity (IncidenceFaceSum) and
   specialization to ORIGINAL winningJoinCoefficient. Check signs, empty faces,
   and why the generators used for the facets exhaust Winning at the meet.
2. Original CertificateConstraint <-> unique split tuple, including quotient
   reindexing and increasing local rank (FivePatternCoordinates,
   FiveCertificateGeneratorEquiv, FiveCoordinateGeometry). No coordinate-order
   invariance under arbitrary permutations is claimed.
3. The final theorem winningJoinCoefficient_five_original_law and the SCC version.
   Every class must have size5, at least2 classes, raw crossing-cut connectivity.
   Check that no model/Euler bridge is left as an assumed hypothesis.
4. Pursue a new concrete unresolved mixed-profile kernel using the universal
   separator identity. Try to kill closure or cover hypotheses before attempting
   a broad generalization. Retain all counterexamples and Lean failure logs.
5. Seek a recurrence for all-five survivors S2..S5=5,35,415,6455 only if it has a
   structural derivation or new falsifiable prediction; no polynomial fitting
   presented as proof. 6455 is NOT A(25,5).

Labels: PROVED-LEAN only with exact source CI pin, PROVED-PAPER otherwise;
VERIFIED-COMP for ordinary finite computations, CONJECTURE for unproved claims,
KILLED for counterexamples. Record disagreements and exact scope on WORKBOARD.

Current local verification:225 modules,3729 audited declarations, only standard
axioms; full root build, source/coverage and both negative guards pass. Python
independent original-position replay checks all126 n10 partitions,254 selected
n15 patterns, and n5 exclusion. n5 coefficient -4 kills removing >=2 classes.
Existing source tests and pinned Sage checks run in CI; local Sage not claimed.
All passing/failing new build logs are saved in this directory. Final CI status
and source commit are authoritative only in the root receipt.

There are two distinct finite replays: verify_original_bridge.py (554 actual
position-join cases) and verify_global_nc_bridge.py (381 independently generated
global NC-catalogue cases). Both should run in CI. See REPORT for exact scopes.

Final CI promotion: PROVED-LEAN at source ba0357de (CI40992099928) and verification
c51b75ab (CI40992346166), all Lean/exact/Sage jobs SUCCESS; both probe runs also
SUCCESS. The root receipt supersedes all older pending status snapshots.
