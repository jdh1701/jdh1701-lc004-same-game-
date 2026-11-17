# Complementary work for Claude

Please read PLAN.md here and the primary 31a286a four-gap proof checkpoint.
New branch baseline: verified a2212dc (PR32; green CI 40890080150).
Your latest observed branch is 9038f6b. GPT owns the Lean coefficient-cancellation
assembly; please avoid duplicating those source edits.

1. Independently recompute A(16,5) and A(18,6) using bounded-deficit face-profile
coefficient extraction, without importing bf_k.c or its answers. Archive code,
controls, arithmetic and formula assumptions. These are independent computations,
not independent proofs of the face-profile enumeration theorem.
2. Audit Lehner, Free cumulants and enumeration of connected partitions,
arXiv math/0110030, Theorem 4.1 and its NC-closure proof. Identify precisely which
part extends to our NC-region-multiplicative signed weights. Do not assume they
are products of classical cumulants over individual color classes.
3. Audit the four-gap paper cancellation proof for all refinements below a target,
especially singleton/triple refinements, wraparound gaps and distinct witnesses.
4. Review Touchard 1952; Stein 1978; Nijenhuis–Wilf 1979 and Lehner's lattice-path
work for an actual recurrence of our connected kernel, not only analogous names.
5. Your redundant_atom route has a known limitation: our length-12 cone test finds
485 crossed-small generated joins with zero coefficient; 311 have a global cone,
455 after NC-component factoring, leaving 30 failures. See primary 31a286a
cone_results.json and cone_probe.py. Avoid assuming a universally redundant atom.
6. Exact polynomial failure does not refute the involution leading asymptotic.
Please correct the KILLED inference in NEGATIVE_RESULTS/WORKBOARD while retaining
the exact-polynomial counterevidence and an explicit status for the asymptotic.

Return commit pins and claim-by-claim evidence. This file is a repository handoff;
GPT has not directly invoked a Claude API or received your response yet.

Update from GPT during this campaign: the refinement-ideal indicator and
winningJoinCoefficient_crossed_four_zero have now passed local Lean 4.19.0,
with both crossing orientations and arbitrary other color multiplicities.
Do not duplicate that cancellation proof. Exact-head hosted CI and combined
audit are being obtained; until then record this as locally checked evidence.
Please prioritize the independent profile computation and NC-component
multiplicativity/Lehner applicability audit.

Further update: independent_deficit6.py now reproduces both requested values
using exact content DP and the face-profile expression (explicit assumption).
A held-out k=7 calculation gives A(20,7)=199207020 and normalized difference
1/1001 from the degree-five interpolation on k=1..6. Please independently
verify or refute this value or the formula's counting bridge, rather than
repeat our small content counts. Six points do not themselves refute a
five-degree polynomial; an ugly interpolant is not evidence of failure.

Touchard's 1952 original has now been inspected in part. His systems count
nesting as connection; our NC closure does not merge a nested matching.
Check the proper-system layer before importing an S_n recurrence. Minimal
all-five NC-connected signed supports in our existing n=10,15 tables have
5 and 35 terms, respectively, all coefficient -1 (receipt here). This suggests
a focused five-occurrence/pentagon-refinement model to test, not a claimed
universal recurrence or identification with linked diagrams.

Focused speculative task: FIVE_BLOCK_HYPOTHESIS.md records a two-size match
with the five-ary Fuss–Catalan numbers. For j>=2, it predicts all-five connected
nonzero coefficients -1 and [b^4]kappa_20=-285. Please try to refute or construct
a bijection with five-uniform noncrossing partitions before extending this fit.
The j=1 coefficient is -4, an explicit anomaly; there is no general proof yet.
