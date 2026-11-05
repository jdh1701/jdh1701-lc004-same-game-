# LC004 — Repository-wide correction and Claude adversarial handoff
Date: 2026-11-04
Scope: SameGame exact distinct-word enumeration only.

## CRITICAL CORRECTION TO PRIOR ALEXANDRIA RESEARCH REPORTS
Earlier handoffs incorrectly treated the raw maximal-run / auxiliary erasure / noncrossing-certificate semantic bridge as an outstanding unproved theorem. It was ALREADY Lean-verified in PR #26 (head 40f100a1982b1706e7d70a5945baf5a807e08ae9; CI run 40758701430), in LC004/RawCertificateEquivalence.lean. The theorem names include raw_max_win_iff_aux_erases, raw_max_win_iff_certificate, and raw_max_win_iff_insertion_history. Do NOT spend further cycles rebuilding this bridge.

Earlier reports also treated the second-diagonal closed form as only a conjecture. PR #27 supplies a Lean proof of winningColorPatternCount (2*k+2) k = k * (2*k+2).choose (k-1) for k>=1, including its noncrossing profile counts. See LC004/SecondDiagonalClosedForm.lean; CI run 40815362365 at proof commit 85458ab6e139d3d5dc207952494f9227bde577ff. This supersedes heuristic formulas in older notes.

## AUDIT METHOD AND SCOPE
Inspected dedicated repo main recursive tree (148 entries, not the full active research), open PR list (30), PR descriptions for #26,#27,#34,#35,#50,#51,#52,#53, selected PR file lists, and recent GitHub Actions records. Many advanced results are on OPEN STACKED BRANCHES, NOT main. Therefore main-tree-only reviews systematically miss them. This is a PR-level reconnaissance, NOT a line-by-line audit of every Lean declaration, script, proof or branch.

## ADVANCED FORMAL AND COMPUTATIONAL RESULTS PREVIOUSLY MISSED
- PR #26: full raw-game iff noncrossing 2/3 certificate equivalence (Lean, hosted CI).
- PR #27: unconditional second diagonal (Lean, hosted CI). Existing combinatorial literature limits novelty claims.
- PR #34: connected signed-weight expansion for original-game labeled counts; PR describes local Lean success and hosted CI pending at time of description. Recheck exact run before promotion.
- PR #35: original all-five signed coefficient law, certificate-to-split-tuple bijection, separating-family Euler identity, SCC recognition. Reported Lean/Sage CI 40992099928 and 40992346166. Connected all-five survivor count 6455 at n25 is NOT full W_25.
- PR #50: seven-class Euler reduction and explicit counterexamples to projected majority closure; computational/paper results, not new Lean declarations.
- PR #51: universal-seven singleton-tripling classification: seven local lemmas Lean-proved, broader recurrence/classification paper-proved with finite exact replay; do not promote the entire claim to Lean.
- PR #52: LC004/FusionStack.lean; global Boolean-stack winning characterization, half-word intersection and continuation-support distinction. Reported Lean CI 41329698273; all 250 active modules and 4266 declarations audited at pinned source 293cdb9766aa386963f59e33db54d43c48317171. Two counting implementations agree through n=26; n=27,28 currently one counting algorithm. Reported W_26(3)=434087233947, W_27(3)=1326879233787, W_28(3)=4055050431933. Not a closed scalar enumeration law.
- PR #53: LC004/FusionHorizon.lean; finite-horizon support soundness and reversal-averaged counts. CI 41336874589 successful at c23423abd24e65f04193607d93d0e5c62117dd33. Non-lumpability witness rules out assuming reversal is a transition automorphism.
- PR #35 had a newer cross-domain probe CI 41939411676 successful; its exact scope is probes, not a general enumeration proof.

## STRATEGY RESET
Stop re-proving the bridge, second diagonal, and baseline word counts. Primary objective: obtain a genuinely useful uniform count of DISTINCT winning words for all n,q from either (A) fusion-stack support distributions and continuation equivalence, or (B) signed connected-join coefficients / higher-profile classification. Benchmark both against the existing counts through n=28. Prove exact equivalence of each proposed compression to the original count; avoid conflating counts of certificates, successful paths, supports, and words.

## QUESTIONS FOR CLAUDE
1. Read the *actual PR branch source*, not main alone, especially PRs 26,27,35,51,52,53. Audit theorem statements, imports, CI receipts, and axioms.
2. Identify the strongest existing general counting identity and the narrowest unsolved mathematical obligation. Determine whether fusion supports already give a useful all-n,q recurrence and what complexity/novelty is lacking.
3. Cross-check global fusion and connected signed-join expansions independently; find a map between their states or a counterexample to such a map.
4. Test whether half-word continuation supports admit a bounded sufficient statistic or whether non-lumpability prevents this.
5. Analyze mixed-profile (5,6), multiple-six, projected ternary constraint complexes, and higher-profile signed coefficients as alternate routes.
6. Return exact GitHub PR numbers, source SHAs, theorem names, build IDs, counterexamples and failures. Separate PROVED-LEAN, PROVED-PAPER, VERIFIED-COMP, and CONJECTURE.
7. Do not assert that the open OEIS enumeration problem is solved without an independently reviewed non-tautological general enumeration result.

## REPOSITORY POLICY
This document is a research audit, not Lean proof code. Formal code is promoted only after green Lean CI at the exact source commit. Claude Chat delivery is separate from GitHub: a committed handoff is not evidence it has been transmitted to a Claude conversation.
