# Old repository → this repository

Old repo: `jdh1701/jdh1701-lc004-same-game-`. Every pull request and branch head is listed with where its content now lives. Nothing was dropped: files identical to an earlier version are kept once, and files that genuinely differ between branches are kept side by side (the mainline copy at the normal path, the others under `archive/variants/<branch>/`).

The mainline is the stacked chain PR #26 → #55 ending at `0990b0e` (review/claude-entropy-audit-20261112). It contains every Lean module from every side branch. The Nov 14 coordination snapshot (#56) is in `coordination/`.

| PR | Head | Date | State before consolidation | Last commit | Now lives |
|---|---|---|---|---|---|
| #1 | `e6d6796` | 2026-09-22 | open | Record compilation of research-path Lean module | `archive/legacy-lineage/` |
| #2 | `c3d8c39` | 2026-09-28 | open | Finish evaluator equation proof and discharge ragged counterexample by cases | `archive/legacy-lineage/` |
| #3 | `1aa8155` | 2026-10-28 | merged | Apply erasure induction hypothesis to winning terminal state | in `main` → this repo |
| #4 | `858cf3f` | 2026-10-28 | merged | Include pair/triple run-length theorem in full Lean build | in `main` → this repo |
| #5 | `5640aeb` | 2026-10-28 | merged | Include complete monochromatic run erasure theorem in Lean build | in `main` → this repo |
| #6 | `7ff0f4f` | 2026-10-28 | merged | Include maximal-run path-to-erasure simulation in complete Lean build | in `main` → this repo |
| #7 | `7707377` | 2026-10-28 | merged | Build raw isolated insertion theorem with full Lean library | in `main` → this repo |
| #8 | `d839563` | 2026-10-28 | merged | Include raw prefix heaviness bridge in Lean root build | in `main` → this repo |
| #9 | `7f9f5a4` | 2026-10-28 | merged | Import arbitrary prefix repetition lemma into Lean build | in `main` → this repo |
| #10 | `3fb1c71` | 2026-10-28 | merged | Fix reserved identifier and complete pushColor heaviness implication | in `main` → this repo |
| #11 | `85bacc0` | 2026-10-28 | merged | Align induction suffix association in arbitrary-position repeat lemma | in `main` → this repo |
| #12 | `c663547` | 2026-10-28 | merged | Import two-encoder agreement theorem for CI verification | in `main` → this repo |
| #13 | `9b38aa4` | 2026-10-28 | merged | Run new theorem axiom reports during complete Lean CI build | in `main` → this repo |
| #14 | `0466784` | 2026-10-28 | merged | Include Lean color-permutation invariance theorem in project build | in `main` → this repo |
| #15 | `1435194` | 2026-10-28 | merged | Include erasure color-equivariance proof in full Lean build | in `main` → this repo |
| #16 | `99600bf` | 2026-10-28 | merged | Add independent RGS coefficient and published-sequence regression tests to CI | in `main` → this repo |
| #17 | `8b20402` | 2026-10-28 | merged | CI-test second diagonal predictions against independent noncrossing enumeration | in `main` → this repo |
| #18 | `233ec23` | 2026-10-28 | merged | Add adversarial overlap classification regression to CI | in `main` → this repo |
| #19 | `c2d6c28` | 2026-10-28 | merged | Import four-block crossing lemma into full Lean build | in `main` → this repo |
| #20 | `8cfc24f` | 2026-10-28 | merged | Add four-block overlap compatibility theorem to complete Lean build | in `main` → this repo |
| #21 | `d0654ce` | 2026-10-28 | merged | Repair dependent induction with generalized reverse-history lifting and eliminate sorryAx | in `main` → this repo |
| #22 | `2bc6475` | 2026-10-28 | merged | Include noncrossing insertion-index theorems in Lean build | in `main` → this repo |
| #23 | `3b7df6b` | 2026-10-28 | merged | Repair dependent list membership case split in noncrossing pair family theorem | in `main` → this repo |
| #24 | `29fc2af` | 2026-10-28 | merged | Repair finite triple-index membership proof in Lean | in `main` → this repo |
| #25 | `840c4c0` | 2026-10-28 | merged | Correct self-crossing restriction: insertion blocks have at most three indices | in `main` → this repo |
| #26 | `40f100a` | 2026-10-28 | open | Prove raw maximal-run wins equivalent to complete noncrossing certificates | mainline chain → this repo |
| #27 | `0b5535a` | 2026-10-29 | open | Assemble general signed-join enumeration over k-class patterns | mainline chain → this repo |
| #28 | `0f32a99` | 2026-10-29 | open | Record verified face decomposition ledger, minimal obstructions, and remaining research qu | mainline chain → this repo |
| #29 | `d586142` | 2026-10-29 | open | Correct Burns–Purcell bibliography against journal and OpenAlex records | mainline chain → this repo |
| #30 | `2869d3e` | 2026-10-29 | open | Certify ternary continuation collision and add pinned REPL, SymPy and Z3 experiments | side branch → `research/`, variants in `archive/variants/` |
| #31 | `16e2fdd` | 2026-10-29 | open | Record n=25 (j=5) all-five connected-kernel count: 6455 (CI 40942806037) | side branch → `research/`, variants in `archive/variants/` |
| #32 | `a2212dc` | 2026-10-29 | open | Formalize four-gap overlap and winning indicator; audit all 171 Lean modules | mainline chain → this repo |
| #33 | `e6dbea5` | 2026-10-29 | open | Add independent deficit-six extraction and full receipts; fix Sage JSON serialization | mainline chain → this repo |
| #34 | `0fb784a` | 2026-10-29 | open | Prove original-game labeled counts have the connected noncrossing expansion | mainline chain → this repo |
| #35 | `c30f80d` | 2026-11-04 | open | Add from-scratch brute-force confirmation of A035617 through n=14 | side branch → `research/`, variants in `archive/variants/` |
| #36 | `f05cfa7` | 2026-10-29 | open | Independent review of original all-five coefficient law (ba0357d, c51b75a): confirmed | side branch → `research/`, variants in `archive/variants/` |
| #37 | `482ff9f` | 2026-10-29 | open | Archive expanded local proof audits, falsification controls and mixed-kernel handoff [skip | mainline chain → this repo |
| #38 | `c6f719c` | 2026-10-29 | open | Archive ten-route attempts, independent collapse traces and exact proof receipts [skip ci] | mainline chain → this repo |
| #39 | `495dce2` | 2026-10-30 | open | Record successful hosted verification, sparse rescue ledger, and high-dimensional core obs | side branch → `research/`, variants in `archive/variants/` |
| #40 | `c685723` | 2026-10-30 | open | Record final proof source, exact replay success and remaining Lean CI [skip ci] | mainline chain → this repo |
| #41 | `d8cb27e` | 2026-10-30 | open | Add winningJoinCoefficient_ne_zero_crossed_class_card_ge_five: the full crossed-class >= 5 | side branch → `research/`, variants in `archive/variants/` |
| #42 | `b04947b` | 2026-10-30 | open | Record green connected-support proof and ten-route verification [skip ci] | mainline chain → this repo |
| #43 | `6744374` | 2026-10-30 | open | Restore complete workboard in verification receipt [skip ci] | mainline chain → this repo |
| #44 | `c98dc7b` | 2026-10-31 | open | Record successful n21 exhaustive census CI receipt [skip ci] | mainline chain → this repo |
| #45 | `ff5d10c` | 2026-10-31 | open | State the multiclass hypothesis in the workboard formula [skip ci] | mainline chain → this repo |
| #46 | `243b4ea` | 2026-10-31 | open | Record verified contraction and completed three-run layer [skip ci] | mainline chain → this repo |
| #47 | `093d3fb` | 2026-10-31 | open | Record verified common-gap proofs and complete primitive-core replay [skip ci] | mainline chain → this repo |
| #48 | `5c1e231` | 2026-10-31 | open | Record hosted two-generator census and precise remaining first-excess obligation [skip ci] | mainline chain → this repo |
| #49 | `27dd0e3` | 2026-10-31 | open | Record verified first-excess boundary lemmas and exact proof inputs [skip ci] | mainline chain → this repo |
| #50 | `a67850c` | 2026-10-31 | open | Record hosted seven-boundary reduction and nonzero obstruction verification [skip ci] | mainline chain → this repo |
| #51 | `92974f6` | 2026-11-01 | open | Record verified seven-class deletion, universal classification and exact-source receipts [ | mainline chain → this repo |
| #52 | `24182d8` | 2026-11-01 | open | Record full fusion verification, scope, failed attempts and handoff [skip ci] | mainline chain → this repo |
| #53 | `c23423a` | 2026-11-01 | open | Verify reversal counting through 28 and preserve failed representative-selection attacks | mainline chain → this repo |
| #54 | `fc5f5e2` | 2026-11-04 | open | docs(LC004): establish shared Claude/ChatGPT coordination CLAUDE_TO_CHATGPT.md | mainline chain → this repo |
| #55 | `0990b0e` | 2026-11-12 | open | Claude review of entropy certificate: reruns pass, H=9 table cannot reach uniform law | mainline chain → this repo |
| #56 | `79c6163` | 2026-11-14 | open | docs: qualify historical fixed-content counting cross-reference | `coordination/` |
| #57 | `b03fa96` | 2026-11-17 | open | Test extra-base-color entropy refinement with exact Bellman certificates | `research/extra_color_state_20261117/` |

## Branches without a PR

- `research/enumeration-audit-2026-10-17` at `233fc19` (2026-10-18)
- `research/face-decomposition-20261028` at `6e5d636` (2026-10-28)
- `research/face-lemma-adversarial-audit-20261028` at `8379ddd` (2026-10-29)
- `claude/github-consolidation-cet7n9` at `5418b1b` (2026-10-29)
- `integration/alexandria-face-lemma-20261029` at `4b7ea92` (2026-10-29)
- `verify/independent-lean-audit-20261029` at `2a3fffe` (2026-10-29)
- `verify/audit-face-decomposition-20261029` at `8ba0a76` (2026-10-29)
- `verify/greedy-obstruction-20261029` at `c8ae538` (2026-10-29)
- `verify/four-gap-cancellation-20261029` at `71e0a74` (2026-10-29)
- `verify/nc-components-20261029` at `4527f7b` (2026-10-29)
- `research/gpt-handoff-review-20261029` at `67c193a` (2026-10-29)
- `exploration/claude-sage-20261029` at `390e4eb` (2026-10-30)
- `audit/entropy-certificate-20261112` at `98a31b2` (2026-11-11)
