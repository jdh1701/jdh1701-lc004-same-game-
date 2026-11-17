# LC004: counting winning words in one-dimensional Same Game

In one-dimensional Same Game you may delete any maximal run of two or more equal letters, and the remaining pieces then join. A word *wins* if it can be erased completely. LC004 asks for an all-length formula for W_q(n), the number of winning words of length n over q colors. For q = 3 this is OEIS A035617, which OEIS marks as unsolved.

The project combines three kinds of work:

- a Lean 4 library of machine-checked theorems
- exact computation, with counts known through n = 28
- written proofs, each recorded with its evidence

John Holden runs the project. ChatGPT and Claude contribute through pull requests.

**Start with [`STATUS.md`](STATUS.md)**. It lists what is proved, what is computed, what has been ruled out and what is still open.

## Layout

| Path | What it holds |
|---|---|
| [`STATUS.md`](STATUS.md) | One-page summary of the current state |
| [`research/WORKBOARD.md`](research/WORKBOARD.md) | The canonical claim registry: every claim, its status, its evidence and its owner, plus the session log |
| [`LC004/`](LC004/), [`LC004.lean`](LC004.lean) | The Lean library: 251 modules, all reachable from the root, with no `sorry` |
| [`research/`](research/) | Every research line, one dated folder each, each with a REPORT and HANDOFF, scripts, data and receipts. The thematic map is [`docs/RESEARCH_INDEX.md`](docs/RESEARCH_INDEX.md). |
| [`coordination/`](coordination/) | How John, ChatGPT and Claude work together ([`PROTOCOL.md`](coordination/PROTOCOL.md)) and the open questions between models ([`OPEN_REQUESTS.md`](coordination/OPEN_REQUESTS.md)) |
| [`docs/`](docs/) | Navigation: the research index, the map from old branches and PRs ([`BRANCH_MAP.md`](docs/BRANCH_MAP.md)), Lean notes ([`LEAN.md`](docs/LEAN.md)) and per-file provenance |
| [`publication/`](publication/), [`blueprint/`](blueprint/) | Paper draft (`paper.tex`) and the blueprint site |
| [`receipts/`](receipts/), [`verification/`](verification/) | Pinned CI and replay receipts |
| [`scripts/`](scripts/) | Repository checks: Lean coverage and source guard, axiom audit, provenance |
| [`archive/`](archive/) | Superseded material, kept for the record: the September–October legacy lineage, alternate versions of files from side branches, and old branch-specific CI workflows. See [`archive/README.md`](archive/README.md). |

## Using it

```bash
# Lean (toolchain v4.19.0, Mathlib v4.19.0)
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean      # standard axioms only

# Repository checks (standard library Python)
python3 scripts/check_lean_coverage.py     # every module reachable, no placeholders or custom axioms
python3 scripts/check_provenance.py        # carried-over files unchanged
```

Each research folder's README, REPORT or HANDOFF says how to rerun its computations.

**Continuous integration.**

- `lean.yml` builds the library and runs the axiom audit and fast regression checks on every push to `main` and every PR.
- `repo-checks.yml` runs the coverage, provenance and index checks.
- The other workflows in `.github/workflows/` replay specific research lines. They were tied to old branch names and now run only by manual dispatch, from the Actions tab.

## Contributing

1. Work on a short branch cut from `main`.
2. Open a PR, and merge it once CI is green. Never stack one branch on another unmerged branch.
3. Record every status change in the WORKBOARD in the same PR.

The details are in [`coordination/PROTOCOL.md`](coordination/PROTOCOL.md).

## History

This layout was consolidated on 2026-11-17 from all 72 branches and 57 PRs of `jdh1701/jdh1701-lc004-same-game-`. Before that, `main` had stopped at 2026-10-28, while 31 open PRs carried the later work. The consolidation commit is a merge whose parents are the old `main` and every branch head, so the full commit history is still reachable. Every distinct file version at every branch head is here. The only exceptions are 37 earlier versions of files that the mainline itself later updated; those stay in the old repository's history.

- **Mainline (PR #26 → #55).** Files sit at their original paths. This chain includes every Lean module written on any branch.
- **Side-branch additions.** Placed at their original paths.
- **Files that differed between branches.** The mainline copy is at the original path. Each other version is under `archive/variants/<branch>/`.
- **The earlier September lineage.** Under `archive/legacy-lineage/`.

[`docs/provenance.json`](docs/provenance.json) records the source branch, commit and Git blob for each of the 1,728 carried-over files. CI run logs for the old branches stay attached to their original commits.
