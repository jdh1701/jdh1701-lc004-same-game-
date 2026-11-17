# LC004 status

Snapshot as of 2026-11-17, including PR #57. This page summarizes the records; it does not certify anything. The canonical claim registry is [`research/WORKBOARD.md`](research/WORKBOARD.md). Each line below points to the folder whose REPORT, HANDOFF or receipts carry the evidence.

**The problem.** In one-dimensional Same Game you may delete any maximal run of two or more equal letters, and the pieces on either side then join. A word *wins* if it can be erased completely. The open target is an all-length counting law for W_q(n), the number of winning words of length n over q colors. For q = 3 this is OEIS A035617, which OEIS lists as unsolved. **The target is still open.**

## Proved in Lean (PROVED-LEAN)

All of these are in the build closure of `LC004.lean`: 251 modules, no `sorry`, standard axioms only. They were green on hosted CI on the commits cited in the folder receipts. **The library has not yet been built in this new repository.** The first CI run here will confirm it.

| Result | Lean name | Evidence |
|---|---|---|
| Winning ⇔ a noncrossing certificate of blocks of size 2 and 3 exists. This recovers Biedl et al. 2002, Thm 2. | `raw_max_win_iff_certificate` (`RawCertificateEquivalence.lean`) | WORKBOARD C0, PR #26 |
| Second diagonal: A(2k+2,k) = k·C(2k+2,k−1) for k ≥ 1 | `winningColorPatternCount_second_diagonal` | WORKBOARD K3, PR #27 |
| Face lemma: a word wins iff its heavy skeleton is noncrossing and every face wins | `winning_iff_heavy_face_decomposition` | WORKBOARD C2, PR #28 |
| A crossed class in a join with nonzero coefficient has size ≥ 5 | `winningJoinCoefficient_ne_zero_crossed_class_card_ge_five` | `claude-own-proof` branch, PR #41 |
| The original all-five coefficient law, SCC recognition and the generator bijection | see `five_bridge_20261029/` | PR #35, final audit: 225 modules |
| Fusion automaton: winning ⇔ ε lies in the Boolean fusion support; wins(u++v) ⇔ support(u) ∩ support(rev v) ≠ ∅ | `raw_max_win_iff_fusionEval` (`FusionStack.lean`) | `global_fusion_20261101/`, PR #52 |
| Fusion horizon (stack-length bound and truncation separation) | `FusionHorizon.lean` | `fusion_horizon_20261101/`, PR #53 |
| Seven `SmallRefinementGap` theorems | `SmallRefinementGap.lean` | `seven_pair_deletion_20261101/`, PR #51 |

## Exact counts (VERIFIED-COMP)

- W₃(n) is known through **n = 28**: W₂₆ = 434087233947, W₂₇ = 1326879233787, W₂₈ = 4055050431933.
  - Two independent methods agree through n = 26.
  - n = 27 and 28 rest on a single method, the half-word count (`global_fusion_20261101/`).
- A from-scratch brute-force counter agrees through n = 14 (`cross_domain_20261029/`). Claude's own independent DP agrees through n = 15 (`entropy_certificate_20261111/claude_review/`).

## Paper proofs with finite checks (PROVED-PAPER, not in Lean)

- **Growth rate.** liminf W₃(n)^{1/n} ≥ 2.99622…, refined to ≥ 2.996273. Exhaustively checked integer certificate; see `entropy_certificate_20261111/`, R20261111C.
- **Five colors.** W₅(n)/5ⁿ ≤ 129·(40/41)ⁿ, so the five-color winning density decays exponentially (`global_fusion_20261101/RUN_BOUND.md`).
- **Face-decomposition counting.** Theorem T, the one-heavy-class Kreweras formula and the j = 1..7 diagonal closed forms (`face_decomposition/`).
- **First-excess layer.**
  - The two-generator stratum is enumerated in full.
  - The universal (7,5,…,5) stratum is classified as singleton triplings, with count (5j+2)·A_j/5 (`two_generator_excess_20261031/`, `seven_pair_deletion_20261101/`).

## Negative results (KILLED / ruled out)

- **Diagonal polynomials.** "A(2k+j,k) = C(2k+j,k−1)·(a polynomial of degree j−1)" fails at j = 6. The involution-number leading-coefficient conjecture fails with it.
- **Heavy-greedy deletion is not safe.** AAABAABBAB wins, but one heavy deletion leaves a losing word. Confirmed in Lean as a finite instance.
- **Finite-summary strategies.** u = AAABBABCCCBC and v = AAABABBCCCBC have equal summaries, yet u+C wins and v+C loses.
- **Ternary losers.** Periodic ternary losers are not all trivial, and ternary losers do not reduce to one letter.
- **Recurrence searches.**
  - 37 polynomial-coefficient recurrence templates and 5 algebraic generating-function templates are excluded on the counts through n = 28.
  - Several of these templates fit the older terms but failed n = 26–28.
  - This does **not** prove the sequence is non-D-finite.
- **H = 9 entropy table.** Under the uniform law, the fixed-policy finite model has an exact worst-case average drift in [138287869, 138287874] / 3·10⁹ ≈ +0.046096. This is strictly positive, so the model cannot certify positive density.
  - An integer Bellman certificate establishes the interval (ChatGPT, `extra_color_state_20261117/`, PR #57). Claude independently replayed it on 2026-11-17.
  - This confirms, exactly, the floating-point +0.0461 from the Claude review of 2026-11-12. The ceiling ≈ 2.99642 is still a floating-point figure.
- **Extra base color.** Remembering one more base color lowers the drift to [132338197, 132338202] / 3·10⁹ ≈ +0.044113, which is still positive (PR #57, exact).
  - The obvious idea, that one stored color removes all adversarial uncertainty, is false: pops expose an older color that the finite state does not retain.
  - Both results hold only for the fixed lexicographic witness policy in these finite max-adversary models.
- **Fixed-content formula.** (2^(r−3)+1)(r+6)(r+5) disagrees with the fixed-label counts for (3,3,7) and (3,3,8): it predicts 2652 and 6006, the counts are 2340 and 4368.
  - The check was reported but not preserved as code (`coordination/BRANCH_MAP_SNAPSHOT_2026-11-14.md`).

## Open conjectures

- **Positive uniform density.** W₃(n)/3ⁿ is positive in the limit and the growth rate is exactly 3.
  - Evidence: the density rises at every computed length from n = 10 to 28.
  - Falsifier: a persistent decline at n = 29–32.
- **Binary content counts.** B(a,b) is a polynomial in b of degree a for b > a. Checked for a ≤ 6.
- **Cumulant vanishing.** The q^j coefficient of κ_s is zero for s < 5j. Checked for s ≤ 15.

## Open obligations

These are in order of leverage.

1. **First excess.** Rule out a nonzero connected first-excess pattern that has no three-run and at least 3 original certificates (`two_generator_excess_20261031/HANDOFF.md`). The higher-excess layers are open beyond that.
2. **Lean for the growth bound.** Formalize finite-table lifting and policy induction for the entropy certificate, against the `FusionStack.lean` soundness theorems.
3. **Entropy method.** Two experiments are next:
   - Optimize over *all* valid witness choices in the extra-color model, not only the lexicographically first. If the drift stays positive, keep a longer base suffix (PR #57's proposed next step).
   - Separately, compute exact uniform drift intervals for H = 5…9, to see whether the drift trends toward zero.
4. **Second method for n = 27, 28.** A second, independent count for these two terms.
5. **Review request R-2026-11-04.** Questions 1, 3, 4 and 6 are unanswered; 2 and 5 are partly answered. See [`coordination/OPEN_REQUESTS.md`](coordination/OPEN_REQUESTS.md).
