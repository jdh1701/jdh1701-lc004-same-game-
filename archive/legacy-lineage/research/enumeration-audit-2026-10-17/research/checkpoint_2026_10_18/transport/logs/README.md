# Literal execution evidence

All `.log` files are actual command output, not reconstructed transcripts.
Failed attempts remain in the record and are not accepted proofs.

- `coefficient_attempt1.log`: failed rewriting of the coverage equivalence.
- `separated_attempt1.log`: replay of that locality error; product module blocked.
- `separated_attempt2.log`: locality and generic transport compiled; the
  separated-partition module failed on implicit binders and type inference.
- `separated_attempt3.log`: successful build of locality, transport, and
  separated-partition modules after the binder/type fixes.
- `full_board_attempt1.log`: successful build including the concrete
  full-board splitting and conditional coverage-transfer theorem.
- `axioms_verified.log`: signatures and axiom dependencies for all 23 new
  named theorems, generated from the current compiled modules.
- `prior_art_comparison.log`: coefficient-by-coefficient matches with the
  transcribed OEIS formulas at lengths 12–15.
- `source_audit.log`: theorem inventory, source hashes, axiom validation,
  fixed stage counts and explicit unproved boundary.

Local Lean commands use `/tmp/lean-4.19.0-linux/bin` and the existing
`/tmp/samegame-proc-self-compat.so` shim to repair executable-path lookup
through `/proc/self/exe`. The shim changes no proof or kernel behavior.
GitHub CI uses its normal pinned Lean installation without the shim and
checks the whole project. Local module builds are targeted, not full-root
builds, because the aggregate Mathlib object is absent from the local cache.
