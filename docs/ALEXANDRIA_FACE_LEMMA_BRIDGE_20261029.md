# Alexandria ↔ LC004 signed-join verification bridge

Source: `proof/second-diagonal-counting-20261028`, Lean 4.19.0. This branch is isolated from the existing proof branch.

## Existing kernel-checked mathematical substrate
- `LC004/CertificateConstraintJoins.lean`: `winning_pattern_upward_closed`, `constraintIndicator_join`, `constraint_join_union_update`.
- `LC004/CertificateJoinIteration.lean`: `certificateJoinTerms_score`, `certificateJoinTerms_winning_indicator`.
- `LC004/WinningJoinCount.lean`: `winningColorPatternCount_signed_joins`.

The original proof branch's Lean Proof Check run 40816780596 succeeded. This is evidence for that exact checked commit, not for any future Face Lemma.

## Face Lemma boundary
The signed-join identity itself does **not** imply independent face factorization. A face decomposition theorem needs explicit:
1. A face carrier (subset of positions) and a partition of the relevant positions.
2. A restriction map on color patterns/certificates.
3. A precise no-crossing condition for heavy certificates (class size at least four).
4. A gluing/factorization lemma with hypotheses sufficient to prevent double counting.
5. A proof that the decomposition preserves the winning predicate and class-count constraints.

Do not silently assume arbitrary restrictions preserve noncrossing certificates. Test counterexamples for small n before stating a universal theorem.

## Verification gate
Compile the original imports with the repository-pinned Lean 4.19.0 toolchain. Do not claim that `#print axioms` alone establishes the absence of every unwanted dependency; inspect its output and the theorem's imports.

## Integration
Alexandria Core should ingest exact repository/ref/path/blob SHA and CI run IDs, never a paraphrase of the theorem as its certificate. A research result must carry a claim-bound formal receipt, including exact Lean toolchain and declaration identity.

## Next implementation
Implement a finite face-boundary counterexample model and compare it with the existing LC004 certificate semantics. Only then propose a typed Lean theorem statement. This document adds no new theorem.
