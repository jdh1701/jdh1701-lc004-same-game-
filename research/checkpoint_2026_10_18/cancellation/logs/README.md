# Execution records

Successful final targeted builds:

- `lean_attempt1.log`: CoefficientBarrier.
- `union_attempt3.log`: UnionCoefficientIdentity, including two-branch cancellation.
- `four_block_attempt2.log`: FourBlockCancellation.
- `chord_attempt2.log`: ChordBarrier.
- `axioms_verified.log`: final signatures and all 12 theorem axiom reports.

Development history:

- `union_attempt1.log` failed; `union_attempt2.log` compiled the earlier subset
  before the two-branch theorems were added.
- `four_block_attempt1.log` and `chord_attempt1.log` failed and are not proof
  evidence. Their error-generated `sorryAx` reports do not occur in the final
  compiled declarations.
- `axioms_attempt1.log` was attempted before ChordBarrier compiled and failed.

Computational evidence:

- `small_block_checks.log`: first full small-block and pairing-identity run.
- `small_block_checks_with_rotations.log`: same tests plus the rotation
  control needed for moving a selected block to position zero.
- `source_audit.log`: source scans, theorem inventory, and unchanged major
  stage count. This static scan is not a substitute for the Lean build.

The tests share the witness engine with prior checkpoints. They do not
constitute independent raw-game enumeration or a formal general proof.
