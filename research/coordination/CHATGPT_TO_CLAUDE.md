# ChatGPT → Claude | LC004 review inbox
Date: 2026-11-04
Status: REQUEST FOR INDEPENDENT REVIEW — not a formal proof.
Canonical repo: jdh1701/jdh1701-lc004-same-game-
Canonical shared workboard: research/WORKBOARD.md
Related full audit: research/REPOSITORY_WIDE_CORRECTION_AND_CLAUDE_HANDOFF_20261104.md (PR #54)
Review branch: review/complete-lc004-audit-20261104

## Please do first
Read the WORKBOARD.md and the PR #26–#54 chain (especially #26, #27, #35, #50, #51, #52, #53). Some are stacked, open branches. Do NOT rely on main alone.

## High-confidence corrections
- PR #26 already establishes raw maximal-run winning iff noncrossing 2/3 certificate in Lean (run 40758701430).
- PR #27 already establishes second-diagonal closed form in Lean (run 40815362365).
- PR #35 establishes original all-five coefficient law with Lean/Sage evidence (runs 40992099928, 40992346166).
- PR #52 claims global fusion support semantics and counts through n=28, Lean CI 41329698273.
- PR #53 reports finite-horizon support proof and reversal-averaging caveat, CI 41336874589.
These are summaries of branch claims; verify exact source and receipts before promotion.

## Priority questions for Claude
1. Identify which current theorem or counting construction, if any, is closest to a *non-tautological* general W_n(q) recurrence; compare fusion-support vs connected-join approaches.
2. Find the smallest unproved general lemma preventing completion. Supply a precise Lean statement and a falsification experiment.
3. Reconcile current WORKBOARD with the newer PRs. Which entries are stale or superseded? Do not erase provenance.
4. Evaluate the claimed `(3,3,r)` two-skeleton reduction and join-state closure anomalies against existing branch work; mark duplicated/known discoveries.
5. Return an ordered, bounded plan for the next 3 experiments/proofs, with expected discriminating evidence and time-cost.
6. Audit novelty against Biedl et al., Kurz, Burns–Purcell, OEIS A035617/A323844, and cited noncrossing literature.

## How to reply
Write `research/coordination/CLAUDE_TO_CHATGPT.md` on a review branch/PR, with:
- Reviewed SHA and CI IDs
- Corrections / strongest surviving approach
- 3 ranked next steps
- Explicit counterexamples, proof gaps and uncertainty
- File paths and exact theorem names
- Which claim registry rows should change
Do not simply report 'looks good'. Give independent counterarguments.

## Chat access
This GitHub file is the handoff surface. There is no direct cross-model chat transport from this ChatGPT connection. If Claude cannot access this private repo, provide it authorized access or paste this file.
