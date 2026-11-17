# Archive

Nothing in this folder is current. It is kept so that nothing from the old repository is lost. Every file here is byte-identical to its source blob, and `docs/provenance.json` records the source of each one. Do not edit these files. Copy one forward if you need it.

## `legacy-lineage/`

Three branches forked from `main` on 2026-09-22, before the October rebuild of the Lean library. Their Lean code is an earlier, separate formalization. It is **not** compatible with the current `LC004/` and is not built.

| Folder | Old branch / PR | Contents |
|---|---|---|
| `research/consolidated-333-lean/` | PR #2, `c3d8c39`, 2026-09-28 | `consolidated/` (pvsnp_foundation, auditor) and an early Lean evaluator proof |
| `research/enumeration-audit-2026-10-17/` | `233fc19`, 2026-10-18 | The 2026-10-17 and 2026-10-18 enumeration checkpoints (284 files) and 36 early Lean modules (CertifiedPaths, FourGapGeometry, UniqueMedian and others) |
| `claude/github-consolidation-cet7n9/` | `5418b1b`, 2026-10-29 | Claude's consolidation attempt from that lineage: `post_theorem/`, `trace_quotient/` and CONSOLIDATION.md. It includes PR #1's post-theorem census. |

## `variants/<branch>/<path>`

These are files whose content on a side branch differs from the copy at the normal path. The copy at the normal path came from the mainline or, for side-branch-only folders, from the newest branch. The variants include:

- **Four alternative `research/WORKBOARD.md` versions.** On 2026-11-17, the 23 session sections that appeared only in these versions were merged into the canonical `research/WORKBOARD.md`, each tagged with its source branch. The pre-merge mainline WORKBOARD is kept at `variants/review/claude-entropy-audit-20261112/research/WORKBOARD.md`.
- **Older root import lists (`LC004.lean`) from side branches.** Every module they import is in the current root.
- **Alternate versions of `face_decomposition/`, `free_cumulants/`, `five_bridge_20261029/` reports, CI receipts and logs.**

## `side-branch-workflows/<branch>/`

These are GitHub Actions workflows that existed only on side branches, or differed there. They are inert here: GitHub reads only the root `.github/`.
