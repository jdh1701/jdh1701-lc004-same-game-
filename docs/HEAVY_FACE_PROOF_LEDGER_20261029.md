# Verified heavy-face proof ledger

Proof source: `5f4d56e608ea6fc024aca91af514c95ec33f6871`. Pinned Lean 4.19.0; [hosted full build and audit passed](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40828254711).

The 19 declarations below include supporting lemmas. The substantive milestone is actual geometric locality, forward winning preservation, and injectivity of certificate restriction. The full converse and enumerative theorem are not proved.

All 588 imported project declarations passed the transitive axiom allowlist (only `propext`, `Classical.choice`, `Quot.sound`). No placeholders, custom axioms or native decision oracle appear in active project source. These results are Lean certificates, not independent novelty certificates or Core-authority receipts.

| Declaration | Complete source | Status |
|---|---|---|
| `certificate_rigid_block_eq_class` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L7) | Verified locally and hosted |
| `patternClassPositions_eq_of_related` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L58) | Verified locally and hosted |
| `heavy_ne_rigid` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L76) | Verified locally and hosted |
| `certificate_heavy_face` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L85) | Verified locally and hosted |
| `rigid_faces_no_alternation` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L119) | Verified locally and hosted |
| `certificate_face_saturated` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L134) | Verified locally and hosted |
| `facePathLocality_of_edge_saturation` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L144) | Verified locally and hosted |
| `heavy_certificate_face_path_locality` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L170) | Verified locally and hosted |
| `heavy_certificate_restrict_join` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L181) | Verified locally and hosted |
| `heavyFaceEmbedding_carrier` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L202) | Verified locally and hosted |
| `canonical_heavy_face_restrict_join` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceGeometry.lean#L212) | Verified locally and hosted |
| `rigid_face_iff_no_rigid_arc_separator` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/RigidFaceArcCriterion.lean#L8) | Verified locally and hosted |
| `restrict_pattern_class_card` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceRestriction.lean#L7) | Verified locally and hosted |
| `certificateConstraint_restrict` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceRestriction.lean#L26) | Verified locally and hosted |
| `winning_restrict_heavy_face` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceRestriction.lean#L43) | Verified locally and hosted |
| `raw_win_heavy_face_word` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceRestriction.lean#L60) | Verified locally and hosted |
| `certificate_position_rigid_or_heavy` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceReconstruction.lean#L6) | Verified locally and hosted |
| `certificate_rigid_related` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceReconstruction.lean#L19) | Verified locally and hosted |
| `certificate_pattern_determined_by_heavy_faces` | [Lean source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/5f4d56e608ea6fc024aca91af514c95ec33f6871/LC004/HeavyFaceReconstruction.lean#L34) | Verified locally and hosted |

## Remaining boundaries

* Global construction from independently winning face certificates: open.
* Full winning iff with explicit no-singleton assumption: open.
* Product equivalence, slot bijection, automorphism accounting, and profile coefficient theorem: open.
* General multi-color enumeration and independent mathematical-priority assessment: open.

Source hashes and machine-readable declaration identities are in `research/heavy_face_proof_ledger.json`; compile/audit evidence is in `research/verification/`.
