# LC004 shared ChatGPT ↔ Claude coordination
Last updated: 2026-11-04. This is a protocol, not a claim of solved mathematics.

## One canonical source of truth
Use the dedicated LC004 repository, not Alexandria's older copies. The authoritative shared workboard is `research/WORKBOARD.md` on the active stacked research branch. Do not replace its existing claim registry, discrepancy log or ownership table. Read it alongside PRs #26–#54, because main is behind the research branches.

## Exact short instruction to Claude
**"Check what ChatGPT uploaded and give it suggestions to help you."**
Interpret this as: read `research/coordination/CHATGPT_TO_CLAUDE.md` and its linked evidence, inspect relevant PR branches and CI receipts, then write a response into `research/coordination/CLAUDE_TO_CHATGPT.md` on a review branch or PR. Update the workboard only for verified, reconciled changes. Do not assume a GitHub commit automatically appears in either model's chat.

## Workflow
1. ChatGPT posts one dated handoff at CHATGPT_TO_CLAUDE.md, with exact SHAs, theorem names, tests, falsifiers and explicit questions.
2. Claude independently reviews the cited branch sources and CI receipts; replies at CLAUDE_TO_CHATGPT.md, with correction priority and minimal reproducible tests. If Claude lacks write access, return Markdown for the user to paste or upload.
3. ChatGPT reads Claude's committed reply, reconciles disagreements in a new review note, and runs Python / Lean checks before promoting claims.
4. Each proof target has ONE active owner in WORKBOARD.md. Different agents may independently audit the same theorem but must not unknowingly duplicate implementation.
5. Preserve all failed attempts and counterexamples. Distinguish PROVED-LEAN, PROVED-PAPER, VERIFIED-COMP, CONJECTURE, KILLED and RETRACTED.
6. Never claim the open problem solved merely from a decision procedure, certificate inclusion-exclusion or finite counts.
7. Commit documentation to review branches; merge proof code only with green CI on exact commit and inspected axiom audit.

## Sync contract
Canonical path: `research/coordination/` in jdh1701/jdh1701-lc004-same-game-.
Alexandria_Omega_New/LC004/coordination/ is a *readable mirror* of the most recent ChatGPT handoff, not an independent authority. Include source SHA in each mirror. Claude's response is not considered received until it is visible through the connector or explicitly pasted into chat.

## Focus
The semantic certificate equivalence and second diagonal are already proved on PRs #26/#27. The highest-risk unresolved task is a useful uniform distinct-word counting law, with fusion-support methods (PRs #52/#53) and connected signed-join coefficients (PRs #35/#50/#51) as primary competing tracks.
