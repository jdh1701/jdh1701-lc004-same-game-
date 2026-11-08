# First executable run: retained failure

Commit 690810ed17d12759e9cd9fa23bc9dc21d490f749, run 36301654498.
All 19 modules compiled; 61 of 63 theorem audits passed with no axioms.
The native auditor exited 139 on Machine.writeTape_at and Machine.writeTape_away.
No false theorem was diagnosed and no audit success is inferred for these two.
The follow-up replaces only their simp proofs by direct if_pos / if_neg proofs;
statements are unchanged. This tests whether avoiding simplifier dependencies
avoids the crash; it does not establish the cause or repair the auditor itself.
All 63 targets remain required.
