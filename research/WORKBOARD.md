# LC004 shared workboard (living document)

This file is the single shared work-in-progress surface for every agent on
this repository (Claude, GPT/Codex, and John). Any agent may edit it. Keep it
current; it outranks older journals and notes when they disagree.

Latest reconciliation: see **GPT handoff review, 2026-10-29** below. Historical
entries are retained; corrections there supersede their status summaries.

## Protocol

1. **Status vocabulary.** Use exactly one per claim:
   - `PROVED-LEAN`: theorem in the build closure, CI green on the cited commit,
     axiom audit passed. Cite commit SHA and Actions run ID.
   - `PROVED-PAPER`: complete written proof, not machine-checked. Cite the file.
   - `VERIFIED-COMP`: exact computation over a stated finite range. Cite script and range.
   - `CONJECTURE`: survived falsification attempts; cite the test and range.
   - `KILLED`: refuted; cite the counterexample.
   - `RETRACTED`: a claim we made and withdrew; keep the row, give the reason.
2. **No Lean claim without a green run on the exact commit.** A commit message
   is not evidence. A red head means the latest claims are unverified.
3. **Kill-first.** New claims enter as CONJECTURE and get an adversarial gate
   before promotion. Record kills; they are results.
4. **Frozen audits.** During an audit, change nothing until the full failure
   map is written in the Discrepancy log. Then correct.
5. **Ownership.** Put your agent name in `Owner` before starting a Lean target;
   remove it when you stop. One owner per target avoids duplicate work.
6. **Log.** Append one line per session to the Change log: date, agent, what changed.
7. **Novelty.** No novelty claim without a logged search. "Not found" is not priority.

## Current verified state (2026-10-28)

| Item | Value |
|---|---|
| Counting branch head | `8d8f647` (PR #27, draft) |
| CI on head | run 40811399447: green, including build-closure check and project-wide axiom allowlist |
| Last red streak | 21 consecutive red runs, `e1176e1` through `d5bd5fe`. The commits claiming the unconditional assembly (`aac77e8`, `d9ae387`) were red when pushed |
| Structural branch | PR #26, head `40f100a` |
| `main` | `10a2c94`, behind both PRs |

## Claim registry

| ID | Claim | Status | Evidence | Owner |
|---|---|---|---|---|
| C0 | Winning (maximal-run) iff noncrossing 2/3 certificate | PROVED-LEAN | `raw_max_win_iff_certificate`; published as Biedl et al. 2002 Thm 2 | — |
| C1 | Classes of size 2/3 are certificate blocks | PROVED-LEAN | `certificate_small_block_eq_class` | — |
| K3 | A(2k+2,k) = k·C(2k+2,k−1), k ≥ 1 | PROVED-LEAN | `winningColorPatternCount_second_diagonal`, 8d8f647, run 40811399447 | — |
| C2 | Face lemma: win iff rigid skeleton NC and every face word wins | PROVED-PAPER, VERIFIED-COMP | `face_decomposition/NOTE.md` Step 2; all patterns n ≤ 12 + 200k random to length 60 | open |
| C4 | Goulden–Jackson type/cotype count | published | GJ 1992; Krattenthaler–Müller 0704.0199 Thm 5; checked N0 ≤ 11 | open |
| C5 | Rotation averaging of the outer face | PROVED-PAPER, VERIFIED-COMP | NOTE.md Step 4; N0 ≤ 11 | open |
| T | Face decomposition counting theorem | PROVED-PAPER, VERIFIED-COMP | NOTE.md; rows n ≤ 15 exact, per-profile n = 14 (27/27), n = 16 (44/44) | open |
| K2 | One heavy class: Kreweras × c_s(b)/b | PROVED-PAPER | NOTE.md | open |
| K4 | Diagonals j = 1..7 closed forms | PROVED-PAPER (finite sums + degree bound), VERIFIED-COMP k ≤ 40 | `diag_formula.py`, `diag_formula.json` | open |
| K5 | Leading term I_j·k^(j−1)/j! (involutions) | PROVED-PAPER | NOTE.md | open |
| K6 | Second coefficients of T(b,m) (A323844) | PROVED-PAPER, VERIFIED-COMP k ≤ 39 | NOTE.md | open |
| P16 | A323844 conjectured polynomials m = 12..16 are correct | VERIFIED-COMP (exact brute force) | `bf.c`, `audit/prof16.txt` | — |
| D1 | A(n,2) = 2^(n−1) − n·F(n−2) − (3+(−1)^n)/2 | published (Burns–Purcell 2007) | matches brute force n ≤ 15 | — |
| H1 | Binary content counts B(a,b) polynomial in b of degree a for b > a | CONJECTURE | a ≤ 6, words ≤ 22 (`audit/kappa2.c`) | open |
| H4 | Periodic ternary losers are trivial | KILLED | aabcaabc | — |
| H5 | Ternary losers reduce to one letter | KILLED | residues of every length occur, n ≤ 13 | — |
| OPEN | Closed form for fixed q ≥ 3 (A035617) | open problem | reduced to heavy kernel (all classes ≥ 4) | open |

## Lean target queue

| Priority | Target | Spec | Notes | Owner |
|---|---|---|---|---|
| 1 | C2 face lemma | `lean_targets/FaceLemma.lean.txt` | structural; reuses C0, C1 | open |
| 2 | Kreweras general type formula | — | the cycle-lemma machinery on PR #27 already covers two profiles; generalize | open |
| 3 | C4 Goulden–Jackson count | — | largest piece; mathlib has no noncrossing partitions | open |
| 4 | T, then K2, K4 (j = 3) | NOTE.md | after 1–3 | open |

## Discrepancy log

| # | Found by | Discrepancy | Resolution |
|---|---|---|---|
| X1 | Claude | Journal at a734a54 counted 131 modules; 5 were outside the build closure | Retracted in REVIEW_CORRECTIONS; CI now checks closure (143/143 reachable at 8d8f647) |
| X2 | Claude | Journal omitted Biedl et al. and Kreweras | Fixed in REVIEW_CORRECTIONS |
| X3 | Claude | Claude's own novelty claim covered all diagonals; A323844 already lists the leading coefficient (j = 0, 1) | Narrowed to T, j ≥ 2, K5, K6 |
| X4 | Claude | Claude's harness: a row script printed "match" without comparing (n ≤ 10); a 64-bit key overflow voided one n = 16 run | Both fixed and rerun |
| X5 | Claude | 21 red CI runs on the counting branch while commit messages described completed assemblies | Resolved by 8d8f647 (green). Rule 2 added to the protocol |
| X6 | Claude | Journal stated the target for k ≥ 2; the formula holds at k = 1 | Lean theorem now covers k ≥ 1 |

## Novelty search log

| Date | Agent | Query or source | Result |
|---|---|---|---|
| 2026-10-28 | Claude | OEIS A035615, A035617, A065237–A065243, A323844, A324128, A066345 | Counts and Kurz polynomials; leading coefficient formula (A238879); no diagonal formula beyond the leading one; q ≥ 3 marked unsolved |
| 2026-10-28 | Claude | Biedl et al. 2002; Burns–Purcell 2005/2007; Kurz 2001 | Characterization and binary count only |
| 2026-10-28 | Claude | Web: clickomania/same game enumeration, Kreweras + game, noncrossing + Same Game, combinatorics-on-words reductions, arXiv 2026 (2608.11290, 2605.19063) | Nothing on face decomposition, diagonals j ≥ 2, or second coefficients |
| — | open | Direct OEIS search for the triangle 1;1;1,2;1,5;1,12,5;1,28,21;1,62,84,14 | Blocked from Claude's sandbox; needs a manual check |

## Change log

- 2026-10-28 Claude: created this workboard; added `research/face_decomposition/` (theorem, proof, code, audit gates) and `research/lean_targets/FaceLemma.lean.txt`.

## 2026-10-29 free-cumulant branch (research/free-cumulants-20261029)
- C2 face decomposition (`winning_iff_heavy_face_decomposition`): PROVED-LEAN on PR #28 (0f32a99); independent rebuild + audit run 40832788563 (162 modules, 1913 decls, standard axioms only).
- R2 `join_small_class_no_cross` (in a join of NC 2/3 certificates, a class of size <= 3 is never crossed by another class): PROVED-LEAN, commit 9d494fe, standard axioms only. Not yet imported into LC004.lean.
- R1 `small_class_eq_of_refines` (a refinement with all classes >= 2 agrees with the coarser pattern on classes of size <= 3): PROVED-LEAN, run 40837815906, axioms propext/choice/Quot.sound.
- kappa_s(q) polynomial in q, q^j coefficient (j >= 2) zero for s < 5j, s <= 15: VERIFIED-COMP (run d4e19c2). General law: CONJECTURE.
- "kappa_s linear in q": KILLED (fails n = 10: 305 vs 300).
- Rows 16-17 not computed (process killed). Novelty unchecked (OEIS fetch blocked).
- Process notes: PR #28's branch audit covers only the closure of HeavyFaceCertificateProduct; merge order must be #26 -> #27 -> integration -> #28; claude/github-consolidation-cet7n9 is 131 commits behind main, do not merge naively.
- Z3 pair-join search (run 40840495698, z3 4.13.4): two NC 2/3 certificates whose join has a crossing with a crossed class of size <= 3: UNSAT for n = 8..12 (agrees with proved R2); size <= 4: SAT at every n = 8..14. Witness n=8: {0,1,4,5} x {2,3,6,7} from (01)(27)(36)(45) and (05)(14)(23)(67). So the earlier "crossed blocks >= 5" statement is KILLED; the correct tight bound is >= 4 (R2 proves >= 4). Bounded evidence, two certificates only. The cumulant vanishing law (q^j coefficient zero for s < 5j, j >= 2) is a separate, still-CONJECTURE statement about cancelled Mobius coefficients, not about class size.
- Project-wide audit with R1/R2 imported (run 40840495706, commit 2c735b4): 163 modules, 0 errors, 0 sorry, AXIOM AUDIT PASS 1928 declarations (propext/choice/Quot.sound only), COVERAGE PASS.
- Diagonals (VERIFIED-COMP, CONJECTURE for general form): A(2k+j,k) = C(2k+j,k-1)*P_j(k) with P_1=1, P_2=k (proved in Lean), P_3=(2k-1)(k+2)/3 (matches 6 points, 3 free parameters), P_4=(5k^3+17k^2-5k-5)/12 (matches 5 points, 4 parameters: only ONE independent check). deg P_j = j-1 is a pattern, not a theorem. Prediction A(16,6)=603148 CONFIRMED by independent sharded brute force (bf_k.c, run 40844840701; same run reproduces A(15,6)=88088 and A(16,7)=56056). So P_4 now has 2 independent checks. research/free_cumulants/diagonals.py.
- A(17,6)=3817996 and A(17,8)=19448 by sharded brute force (run 40845039745). A(17,8)=C(17,7) validates the method. j=5: quartic P_5=(13k^4+85k^3+75k^2-155k+42)/60 fitted on k=1..5 predicts A(17,6) exactly (the 6th point, quintic term 0): ONE genuine check. Pattern deg P_j = j-1 now holds for j<=5 (VERIFIED-COMP, CONJECTURE in general; not in Lean).
- Structure of P_j (VERIFIED-COMP j<=5, CONJECTURE): P_4 and P_5 have NO rational roots (P_3=(2k-1)(k+2)/3 does), so they are not simple products. Leading coefficient of P_j times j! is 1, 2, 4, 10, 26 for j=1..5 = involution numbers (OEIS A000085 as far as I recall; unchecked online). Conjecture: P_j(k) ~ (I_j/j!) k^(j-1), i.e. A(2k+j,k) ~ C(2k+j,k-1) k^(j-1) I_j/j!, egf exp(x+x^2/2). Prediction: leading coeff of P_6 is 76/720 = 19/180. Short data (5 terms); a coincidence is possible.
- Sharded brute force run 40846143245: A(16,5)=2306780, A(17,5)=11417880, A(18,6)=23078316; validation A(18,9)=4862=Catalan(9) OK. NEGATIVE: the degree-(j-1) polynomial pattern BREAKS at j=6. Interpolating C(2k+6,k-1)*P(k) through k=1..6 gives ugly coefficients (denominators 2002, 13104, ...) and leading coefficient 76061/720720, not the involution prediction 19/180 = 76076/720720. Conclusion: "A(2k+j,k)=C(2k+j,k-1)*poly of degree j-1" is KILLED as a general law (holds j<=5 only, with the j=3..5 fits having 3, 1-2 and 1 checks); the involution-number leading-coefficient conjecture is KILLED/unsupported. Caveat: the j=6 points k=5,6 come from one method (brute force) without a second independent check, though the same code reproduced seven known/validated entries. Data in research/free_cumulants/rows_extra.txt.

## 2026-10-29 review of GPT pushes (research/heavy-greedy-obstruction-20261029 / PR #30, publication/alexandria-blueprint-20261029 / PR #29)
- Heavy-greedy obstruction (AAABAABBAB wins; deleting the AA at [4,6) leaves AAABBBAB, which loses; family A^r B A^s B^t A B vs A^r B^(t+1) A B): VERIFIED independently by my own Python solver (4 parameter triples) and by Lean on CI (verify/greedy-obstruction-20261029, run 40886782065: 0 errors, 0 sorry, axioms propext/choice/Quot.sound). Statements are non-vacuous (RunSolvable/Step on the executable run state). The infinite family itself is NOT in Lean (GPT says so).
- Ternary continuation collision u=AAABBABCCCBC, v=AAABABBCCCBC: both lose, equal summary, u+C wins, v+C loses: VERIFIED by my solver and in the same Lean run.
- Word-Hankel ranks q=3, d=2,3,4 = 13, 37, 103 (dims 13, 40, 121): REPRODUCED by my own modular elimination (lower bounds). d=5 (268) not rechecked.
- GPT's OpenAlex access succeeded anonymously (my session's allowlist blocked it). GPT states empty OpenAlex hits are NOT evidence of novelty. Burns-Purcell authorship correction (Chris Burns, Benjamin Purcell; title includes "binary") taken from GPT's journal/OpenAlex check; I did not re-verify it.
- Publication branch: infrastructure only (paper.tex 37 pp, blueprint adapter). GitHub Pages deployment is BLOCKED by a repo setting: Settings > Pages > Source = GitHub Actions (owner action). I did not rebuild the PDF.
- Both branches still hold only a negative result about a greedy/finite-summary strategy; no counting law.
- Crossing coefficients (my computation): c({0145}{2367}) = 0 at n=8, although it is a join of two certificates. Joins with a crossing and nonzero c first appear at n=10, profile (5,5), total c=-5. So the right statement is about NONZERO coefficients, not about which joins exist (see the Z3 entry above). Extending to n=11,12 running.
- Crossing-coefficient law (VERIFIED-COMP n<=12 via research/free_cumulants/crossing_profiles.py, CONJECTURE in general): every join x with a crossing and c(x)!=0 has ALL crossed classes of size >=5. Data (crossed-class size profile: sum of c, number of x): n=10 (5,5): -5, 5; n=11 (5,6): -22, 22; n=12 (5,5): -60, 60; (5,7): 60, 48; (6,6): -30, 30; none at n<=9. R2 (Lean) proves only >=4 for joins to exist; the extra step 4 -> 5 is a Mobius cancellation (e.g. c({0145}{2367})=0 at n=8) and is the real target lemma: show c(x)=0 when x has a crossed class of size 4. This is consistent with, and probably the source of, the cumulant vanishing law s<5j.
- n=13 (same script): crossing_nonzero=585, min crossed class size still 5; profile (sum c, count): (5,5): -65, 65; (5,6): -286, 286; (5,8): 286, 91; (6,7): 117, 143. VERIFIED-COMP n<=13. Note sums like 65 = 5*13, 286 = C(13,3) look structured (unexplained).

## GPT handoff review, 2026-10-29

Owner: GPT/Codex. Scope: handoff revision, provenance review and cyclic-orbit test.
No new Lean theorem or full novelty search is claimed in this session.

### Discrepancies recorded before correction

| ID | Disagreement | Resolution |
|---|---|---|
| G1 | Exact polynomial failure was used to kill the involution asymptotic | RETRACTED that inference. An asymptotic can hold for a nonpolynomial rational function. Universal asymptotic remains a separate paper-proof audit / conjecture, not refuted by these values. |
| G2 | Handoff requires a CI run ID for every kind of claim | Separate status from evidence. CI acceptance checks code and kernel results; literature and paper reasoning need their own sources. |
| G3 | Older queue still asks for the already formalized face lemma | Use existing structural proof; focus on crossed-four coefficient assembly. |
| G4 | Fixed merge order omits current PR base relationships | Inspect ancestry and test a concrete integration commit; do not merge by historical list alone. |

### Current evidence reconciliation

- PROVED-PAPER: four-gap signed cancellation argument and cumulant support derivation,
  primary repository 31a286a, research/LC004/2026-10-29-four-gap-cancellation/.
  These are paper arguments, not complete Lean certification or established novelty.
- VERIFIED-COMP: primary checkpoint 31a286a checks signed support through n=15,
  including independent length-15 counts. Repeating n<=13 is not the next priority.
- PR #32, head a2212dc08ca633cb6925208a865493648c237b0a: 31 new Lean theorems;
  local full build (171 modules) and allowlist audit (2,124 declarations) pass.
  Hosted run 40890080150 was IN PROGRESS at review, so this workboard does not
  promote its results to PROVED-LEAN under its hosted-CI rule yet.
- CONJECTURE / unfinished formal target: universal crossed-four coefficient
  cancellation in Lean; the checked split-indicator theorem is a prerequisite.
- Novelty: exact-term web queries were inconclusive. This is NOT evidence of
  priority. Direct OpenAlex/OEIS response archiving remains a bounded task.

### Cyclic-orbit discrimination

VERIFIED-COMP, n=13, local exact TSV from signed_support.cpp at primary commit
31a286a. Script and receipt: handoff_review_20261029/cyclic_orbits.py and
cyclic_orbits_n13.json. Each crossing pattern has an orbit of size 13 and its
coefficient is constant on that orbit.

| Crossed profile | Orbits | Coefficient distribution by orbit | Total signed sum |
|---|---:|---|---:|
| (5,5) | 5 | 5 at -1 | -65 |
| (5,6) | 22 | 22 at -1 | -286 |
| (5,8) | 7 | 5 at 2, 2 at 6 | 286 |
| (6,7) | 11 | 6 at 2, 1 at 1, 4 at -1 | 117 |

This explains the common factor 13. It does not prove a binomial formula or
explain all orbit counts. The revised handoff asks for orbit and rigid-insertion
analysis before further sequence fitting.

- 2026-10-29 GPT/Codex: read the handoff and full workboard, verified current PR
  bases/heads and PR32 CI state, corrected the asymptotic retraction, revised
  execution gates, and independently resolved the n=13 sums into cyclic orbits.

## Archive/CI update, 2026-10-29

PROVED-LEAN for the 31 theorem statements in PR #32 at a2212dc08ca633cb6925208a865493648c237b0a: hosted run 40890080150 completed SUCCESS. This supersedes the earlier in-progress entry, and does not promote the unfinished coefficient-cancellation or cumulant-support assembly.

Uploaded all currently retained local four-gap pass/fail/environment logs, hashed manifest and a continuation index under handoff_review_20261029/. Intermediate failed source snapshots were not separately retained. See CONTINUATION_INDEX.md for the exact archive boundary and next proof obligation.

## Solver campaign, 2026-10-29

Source e6dbea580447aae5b8d87a4095a186dc26107bb0, PR33: crossed-four signed coefficient cancellation has passed local Lean, complete build (174 modules), and all-module audit (2240 declarations; standard axioms). Hosted run 40895249874: SageMath 10.10 job PASSED; Lean job still running at this record. Do not promote under the hosted-CI rule until that run completes. The previous 31-theorem baseline remains green at a2212dc, run 40890080150.

VERIFIED-COMP: 117195 refinement-indicator cases; independent bounded-deficit extraction reproduces A(16,5)=2306780 and A(18,6)=23078316, conditional on the face-profile expression. Held-out A(20,7)=199207020 gives normalized difference 1/1001 from a degree-five fit to k=1..6, under the same dependency. Six fitted points alone do not kill a degree-five law.

Read solver_campaign_20261029/PLAN.md, PROGRESS.md, VERIFIED_STATE.json and HANDOFF_TO_CLAUDE.md. OpenAlex DOI metadata succeeded; broad queries were rate-limited; SageCell was blocked, then Sage execution succeeded in CI. Original Lehner 2001/2002 and parts of Touchard 1952 were inspected for NC-component and continued-fraction routes. Mathematical applicability limits are documented.

CONJECTURE: the minimal all-five connected kernel may have a five-ary Fuss-Catalan description for j>=2, predicting [b^4]kappa_20=-285. Only j=2,3 are checked (5,35 terms, all coefficient -1); j=1 is an explicit anomaly (-4). See FIVE_BLOCK_HYPOTHESIS.md. No novelty or universal inference from the two sizes is claimed.

GPT session handoff: coefficient cancellation source work is complete locally, hosted verification pending. Next frontier: NC-component/cumulant formalization and enumeration of the surviving connected kernel. Claude has a complementary repository handoff; no direct Claude API response is claimed.
