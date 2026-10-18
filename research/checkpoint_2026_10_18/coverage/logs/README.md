# Literal development logs

These are actual process outputs. Failed attempts are retained and are not
accepted proofs. A failed build can include successfully compiled dependencies;
the final current build and axiom report establish the accepted source state.

- `embedding_attempt1.log`: failed use of nonexistent cross-sum relation lemma names.
- `embedding_attempt2.log`: successful initial saturated restriction and reconstruction.
- `classification_attempt1.log`: missing decidability/tactic imports and unresolved classification goals.
- `embedding_classification_attempt3.log`: failed relation projection, cardinality simplification and tactic budget.
- `embedding_classification_attempt4.log`: embedding compiled; classification exposed missing transitivity constraints and numeral goals.
- `embedding_classification_attempt5.log`: failed comap simplification and finite pairing validity proofs.
- `embedding_classification_attempt6.log`: remaining comap goals, tactic budget and classical decision-procedure issues.
- `embedding_classification_attempt7.log`: embedding compiled; the classification proof still exceeded its tactic budget.
- `geometry_attempt1.log`: failed placement of a declaration comment before a scoped option.
- `geometry_attempt2.log`: embedding compiled; finite pair-block goals lacked concrete decision instances.
- `coverage_attempt1.log`: exhaustive classification compiled; geometric identities still had propositional simplification goals.
- `geometry_diagnostic.log`: intentional diagnostic printing of residual goals after arithmetic; failed, with no proof-hole workaround.
- `coverage_attempt2.log`: geometry compiled; extension/restriction applications needed explicit carrier maps and coordinates.
- `coverage_attempt3.log`: first successful full-family cancellation build.
- `coverage_final_build.log`: successful current build including the support corollary, with redundant geometry tactics removed.
- `axioms_verified.log`: key signatures and axiom dependencies for all 31 named theorems.
- `nonvacuity_attempt1.log`: failed use of named arguments for implicit relation endpoints.
- `nonvacuity.log`: output of the two concrete examples; an empty file with successful exit means Lean accepted them without diagnostics.
- `source_audit.log`: theorem inventory, source hashes, verified boundary and current stage counts.

Local Lean commands use `/tmp/lean-4.19.0-linux/bin` and the existing
`/tmp/samegame-proc-self-compat.so` executable-path compatibility shim.
The shim changes no proof or kernel behavior. CI uses its normal pinned
installation without the shim. No terminal output is reconstructed.
