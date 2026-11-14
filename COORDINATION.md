# Start here: branch-aware LC004 coordination

This navigation layer supplements the [existing coordination protocol](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/fc5f5e26d1f520f1036d9484cbd81ee0a430a8c2/research/coordination/README.md); it does not replace it or certify mathematical claims. Snapshot date: **2026-11-14**.

## Read before starting work

1. Open [the machine-readable branch map](coordination/branch-map.v1.json). It records immutable heads and observed bases for open PRs #26–#55. Main is behind those research branches. Titles are reported metadata, not verified claims.
2. Refresh the relevant PR's current head through GitHub. If it differs from the pinned SHA, inspect the change before reusing a receipt. This file is a snapshot, not an automatically maintained service.
3. Read the pinned existing workboard and source evidence. Its early tables and later journal entries may disagree; retain history and explicitly reconcile superseded statements.
4. Claim one bounded implementation target in the existing ownership system. Independent review is welcome; duplicated implementation is not.

## The current handoff is partial, not missing or complete

- [Request on PR54](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/fc5f5e26d1f520f1036d9484cbd81ee0a430a8c2/research/coordination/CHATGPT_TO_CLAUDE.md): six broad review questions.
- [Actual response on PR55](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/0990b0e9a86a0adf78bdbf20a78bcceeafae4d39/research/coordination/CLAUDE_TO_CHATGPT.md): entropy checkpoint R20261111C only. Questions 1, 3, 4 and 6 remain open; 2 and 5 are only partly addressed.
- The response file on PR54 remains a placeholder. Identical paths on different branches are not interchangeable.
- The reply reports local reruns and explicitly says it did not inspect Actions. The Actions API returned no runs for its exact head when this snapshot was made. This is not a failed-test claim.

Do not promote the reply's floating-point game-value estimates to certified impossibility statements. A finite downward trend also does not refute a positive asymptotic density. Reconcile precise propositions, not merely agreement between models.

## Next handoff format

Preserve existing files. Add a dated immutable record and index it with: request ID, proposition/obligation IDs, source SHA, exact questions, response SHA, coverage per question, evidence and test scope, unresolved objections, next owner, and completion criteria. Mark partial replies explicitly. Update this snapshot through review when branch heads change.

A commit is a shared artifact, not evidence that either chat received or executed it. This change installs no model transport, credentials, paid API usage, workflow, or automatic claim promotion. It does not merge research branches.

## Earlier Alexandria checkpoint and receipt boundaries

Before creating another theorem inventory, consult [Alexandria PR24](https://github.com/jdh1701/Alexandria_Omega_New/pull/24), pinned here to `032f93b94525717f3ba1bbfd9b989f3247b70c22`. Its [exact-audit README](https://github.com/jdh1701/Alexandria_Omega_New/blob/032f93b94525717f3ba1bbfd9b989f3247b70c22/research/LC004/2026-10-29-exact-audit/README.md), [inventory](https://github.com/jdh1701/Alexandria_Omega_New/tree/032f93b94525717f3ba1bbfd9b989f3247b70c22/research/LC004/2026-10-29-exact-audit/inventory), and [theorem ledger](https://github.com/jdh1701/Alexandria_Omega_New/blob/032f93b94525717f3ba1bbfd9b989f3247b70c22/research/LC004/2026-10-29-exact-audit/THEOREM_LEDGER.md) are historical source/evidence artifacts, not this branch map.

Recounting the 20 declaration-index shards at that pin gives **798 entries: 792 labeled UNVERIFIED and 6 labeled PROVED-LEAN**. The entries separately report compilation evidence for 669 and none for 129. The file inventory contains 164 modules: 124 with reported compilation evidence, 40 without, and 162 marked publication matches. These are counts of stored metadata, not new kernel checks. UNVERIFIED means incomplete assurance in that checkpoint, not that 792 mathematical statements are false or unproved. The six positive labels are not elevated by this cross-reference.

The main publication source pin is `d5861420ee776b9618c56c114a84e7c1c870b16d`; JoinRigidBlocks uses `ea80d599b921d6e0139f8162f0348ade2e7b3d3b`. The index's literal `THIS_CHECKPOINT` for LabeledJoinEnumeration is not a Git SHA: resolve it to the file in the pinned Alexandria checkpoint above, without rewriting the historical entry.

Additional historical mirrors under `research/LC004/` record distinct proof snapshots:
- `2026-10-29-four-gap-lean/PROVENANCE.json`: SameGame `a2212dc08ca633cb6925208a865493648c237b0a`.
- `2026-10-29-coefficient-campaign/PROVENANCE.json`: SameGame `e6dbea580447aae5b8d87a4095a186dc26107bb0`, archive `69c76ea140fcbedb9a627986a2dce5c8dcac0e81`.
- `2026-10-29-noncrossing-components/PROVENANCE.json`: SameGame `7c1c26ceec76a4de681abc39b6a24389888b678e`, archive `3297d880164ece25f89e40a78146965b0b2dd42f`.

Their JSON receipts report source hashes, build/axiom results and sometimes pending hosted CI at creation. They are **not** Core `alexandria-receipt/1` hash-chain records. Their pending statuses were not rechecked by this documentation pass; the general ternary enumeration remains explicitly unresolved in the checkpoint.

[Core draft PR27](https://github.com/jdh1701/Alexandria_Omega_New/pull/27), inspected at `f52c5f9464574f53dada157f0ce3d85fbf1d605e`, instead imports this branch map as one inert `coordination_snapshot_observed` event using Core's existing receipt ledger. Its fixture remains pinned to this repository's original index commit `1131341307d764649d2c591e31c7f3fabf3c972d`. It does not import PR24's theorem index or validate its proof receipts, authenticate source origin, complete review questions, or promote claims.

These layers are complementary: historical theorem/evidence inventory, current branch/handoff navigation, and observation-integrity envelope. Reuse the existing inventory rather than rebuilding it; a future proof-receipt adapter still needs explicit schema mapping and independent verifier execution. This append leaves the machine-readable branch map and all historical records unchanged.
