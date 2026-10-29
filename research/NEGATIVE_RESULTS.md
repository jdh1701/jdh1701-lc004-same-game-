# What does not work, and why (2026-10-29)

Each entry: the idea, the evidence that kills or limits it, the status, and where to reproduce.
Status vocabulary as in WORKBOARD.md. Killing an idea here is a result: it removes a branch of the search.
None of this claims novelty; no OEIS/OpenAlex check was possible from Claude's session.

## Killed by counterexample or exact computation

| # | Idea | Evidence | Status | Reproduce |
|---|------|----------|--------|-----------|
| 1 | Free cumulants kappa_s(q) of the winning-word counts are linear in q | Matches rows n<=9; predicts 305 at n=10 (true 300; which class count was fitted is recorded in NOTE.md) | KILLED | research/free_cumulants/NOTE.md, freecum logic in joins.py/cumulants.py |
| 2 | Joins of two noncrossing 2/3 certificates cannot cross with a class of size 4 ("crossed blocks >= 5" as a statement about which joins exist) | Z3 run 40840495698: size<=4 SAT for n=8..14; explicit witness {0,1,4,5} x {2,3,6,7} from (01)(27)(36)(45) and (05)(14)(23)(67) | KILLED in that form (corrected form: see Open conjectures) | research/free_cumulants/z3_pair_join.py, witness.py |
| 3 | A(2k+j,k) = C(2k+j,k-1) * polynomial of degree j-1 in k, for all j | Holds j<=5 (j=4: 2 checks, j=5: 1 check). j=6 interpolation through k=1..6 has denominators 2002, 13104 and leading coefficient 76061/720720; breaks. Data from sharded brute force runs 40845039745, 40846143245 | KILLED as a general law (caveat: j=6 points k=5,6 from one method) | research/free_cumulants/diagonals.py, rows_extra.txt |
| 4 | Leading coefficient of P_j is I_j/j! (involution numbers) | Fit 1,2,4,10,26 for j=1..5 predicts 19/180 at j=6; the degree-5 interpolation gives 76061/720720, which refutes only the exact-polynomial form | INCONCLUSIVE (asymptotic form not refuted; GPT noted this) | WORKBOARD.md |
| 5 | Greedy deletion is safe if every colour stays heavy (any fixed multiplicity threshold) | GPT: AAABAABBAB wins, deleting AA at [4,6) loses; family A^r B A^s B^t A B vs A^r B^(t+1) A B. Claude re-verified in Python and in Lean (run 40886782065); family itself not in Lean | PROVED-LEAN for the concrete witness; family PROVED-PAPER | research/HeavyGreedyObstruction.lean (branch research/heavy-greedy-obstruction-20261029), verify/greedy-obstruction-20261029 |
| 6 | A finite summary (colour counts, run-colour sequence, #heavy runs, boundary run lengths) determines the next continuation | GPT: u=AAABBABCCCBC, v=AAABABBCCCBC have equal summaries, both lose, u+C wins, v+C loses. Claude re-verified in Python and Lean (run 40886782065) | PROVED-LEAN | research/ContinuationSummaryObstruction.lean |
| 7 | Word-recognizer complexity is bounded | GPT: Hankel ranks q=3, d=2,3,4 = 13, 37, 103 (Claude reproduced mod p); binary control shows rank growth does not rule out a compact scalar formula | VERIFIED-COMP (lower bounds only) | research/tool_grounded_20261029 |
| 8 | Support of the all-five connected kernel is counted by 5-ary Fuss-Catalan numbers 5, 35, 285 (GPT conjecture) | Exhaustive n=20 enumeration (488,864,376 partitions, 48 CI shards, run 40927418509) finds 415 patterns (all c=-1) instead of 285; n=10: 5 and n=15: 35 reproduced exactly | KILLED | research/free_cumulants/five_kernel.cpp, n20_shards.txt |

## Limits and corrections to our own work

* The Lean statement winning_iff_heavy_face_decomposition and the certificate product count certificate partitions of a fixed word, NOT winning patterns; they do not solve the count (PR #28 notes; Claude's independent audit run 40832788563).
* PR #28's branch-specific axiom audit covers only the closure of HeavyFaceCertificateProduct (39 of 160 modules at the time); the project-wide AxiomAudit and the source guard cover the rest.
* Brute-force linear-time facts about one-row Same Game with maximal-run deletion do not transfer to cyclic or non-maximal variants.
* Rows 16-17 via the face-decomposition formula were not computed (process killed for memory). Entries for single k were computed by bf_k.c instead.
* "Bounded UNSAT" from Z3 (S<=3, n=8..12) is evidence only; the universal statement is R2, proved in Lean.

## Open conjectures that survive (VERIFIED-COMP, not proved)

* Crossing joins x with c(x) != 0 have every crossed class of size >= 5 (n<=13). The size-4 case is now PROVED-LEAN by GPT (winningJoinCoefficient_crossed_four_zero), independently re-verified, run 40901719494.
* kappa_s(q) polynomial in q with q^j coefficient 0 for j>=2, s<5j (s<=15).

## Proved in Lean on CI and used above

* R1 small_class_eq_of_refines, R2 join_small_class_no_cross (LC004/JoinRigidBlocks.lean; project audit run 40840495706: 163 modules, 0 sorry, standard axioms only).
* Second diagonal A(2k+2,k)=k*C(2k+2,k-1); heavy-face decomposition (PR #27, #28).
