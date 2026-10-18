# Literal execution evidence

All logs are command output, not reconstructed transcripts. Failed attempts
are retained for provenance and must not be treated as accepted proofs.

- `decomposition_attempt1.log`: failed dependent rewrite across a decidable
  interval predicate; `decomposition_attempt2.log` succeeded after using
  simplification with the proved equivalence.
- `gluing_attempt1.log`: successful witness-splicing construction and proof.
- `four_gap_attempt1.log`: the coverage proofs compiled, but the final
  coefficient theorem needed a local finite carrier instance. This file
  records a failed module build.
- `geometry_attempt1.log`: failed tactic budget and finite-label reduction.
- `geometry_attempt2.log`: interval geometry compiled; remaining label
  simplification hit a recursion limit and left arithmetic goals.
- `regional_attempt1.log`: failed geometry build, with residual propositional
  goals after explicit label reductions. The regional module was not built.
- `geometry_diagnostic.log`: intentional diagnostic printing of the residual
  goals. They were `True ∧ True ↔ True`; the build failed.
- `regional_attempt2.log`: successful build of the completed geometry and
  regional cancellation modules, with two harmless unused-premise warnings.
- `axioms_verified.log`: successful current theorem signatures and axiom
  dependency report for all 24 new named theorems.
- `source_audit.log`: successful inventory, source hashes, axiom validation,
  fixed major-stage counts, and explicit unproved boundary.

Local Lean commands used the pinned toolchain in `/tmp/lean-4.19.0-linux/bin`
and the existing `/tmp/samegame-proc-self-compat.so` compatibility shim, which
only repairs executable-path lookup through `/proc/self/exe`. It changes no
proof or kernel behavior. GitHub CI uses its normal pinned Lean installation
without this shim and checks the full project.
