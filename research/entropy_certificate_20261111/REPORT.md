# LC004: a certificate-based ternary growth lower bound

Research checkpoint R20261111C · 11 November 2026

**Exact enumeration remains unresolved.** This checkpoint gives a paper proof, supported by an exhaustively checked finite certificate, of

\[
\liminf_{n\to\infty} W_3(n)^{1/n}
\;\ge\;\frac{28}{(10^{10}9^{18})^{1/28}}
\;=\;2.9962190503368857\ldots.
\]

Here W₃(n) counts ternary words of length n that can be completely erased by the original one-dimensional Same Game rule. The exact algebraic expression is the result; the decimal is only a display approximation. Since W₃(n) ≤ 3ⁿ, the remaining exponential-rate gap is small. A small rate gap is not a measure of distance to an exact enumeration formula.

This result uses a slightly biased, history-dependent input law. It does **not** prove positive winning density for uniformly random words, growth rate exactly 3, an all-length counting formula, or the earlier conjecture about the uniform length-384 drift expectation. It is not a new Lean-compiled theorem. External mathematical review and formalization remain open. No novelty claim is made.

## 1. Evidence and verification boundary

| Object | Exact receipt |
|---|---|
| Finite control table | `prefix9-1.txt`, 23,129 controls, suffix height 9 |
| Table SHA-256 | `9e2b870282b506b1e730d96faf57179cf54b719ee7d1b2cbebfb058cc37500cb` |
| Text certificate | `tilted10-9.certificate.txt` |
| Certificate SHA-256 | `b9d9be10365446af286adbec4534511fcbfd4e681de39b25de17c4d1d05dec6b` |
| Semantic edge checks | 138,774, all pass |
| Weighted integer inequalities | 46,258, all strictly negative |
| Conditional letter weights | A permutation of (10, 9, 9), denominator 28 |
| Potential scale | 100,000,000 |
| Largest drift numerator | −3,041,932, denominator 2,800,000,000 |
| Maximum absolute potential increment | 811,948,960 / 100,000,000 |
| Potential extrema | −305,399,957 / 100,000,000 and 928,680,070 / 100,000,000 |

`audit_certificate.py` uses only the Python standard library. It checks every state and transition against the defining fusion rule, then checks every drift inequality using arbitrary-size integers. It does not use the optimizer, floating-point tolerances, samples, or the model generator. Its decimal evaluation is not used in any pass/fail decision. The prior pair of checkers (`check_model.py`, `check_weighted.py`) also passes. These are separate local implementations by the same research agent, not independent external review.

The numerical optimizer was a discovery tool. It found a potential that was rounded to integers. The exact rounded inequalities, rather than the optimizer's success status, are the proof certificate. A failed later attempt on a larger model is preserved as a failure, not presented as evidence for a stronger result.

## 2. Mathematical starting point

Represent a proper stack as a word with its top on the right. Proper means adjacent colors differ. On reading color a, a stack ending in a may stay unchanged or lose its last letter; otherwise a is appended. Take the union over all possible stacks. The initial support is {ε}.

The bridge to the original maximal-run game is already present at the pinned repository source:

- Repository: `jdh1701/jdh1701-lc004-same-game-`.
- Source: `c23423abd24e65f04193607d93d0e5c62117dd33`.
- File: `LC004/FusionStack.lean`.
- Theorems: `raw_max_win_iff_fusionEval`, `raw_max_win_iff_fusionReach`, and `fusionEval_pop_all`.

That file uses top-first stacks; reversing the storage convention gives the rule above. The relevant source is preserved in this bundle. Its prior compilation belongs to GitHub Actions run **41336874589**, Lean job **124938471768**. This checkpoint inspected the source but did not rerun Lean or that CI job. Only the soundness direction is needed for the lower bound: an accepting fusion computation is an actual winning word.

Keeping a nonempty subset of the reachable support is therefore safe for a lower bound. It need not preserve all winning continuations and is not an exact finite-state recognizer.

## 3. The finite control invariant

A control i stores a finite nonempty set Sᵢ of proper suffixes. Every suffix has length at most H=9, no nonempty suffix begins in 0, and the common prefix of the set is empty. State 0 is {ε}.

An actual configuration consists of a proper base B, a control i, and a global color permutation. Under that permutation the last base color is 0. The retained stacks are exactly B Sᵢ, translated back to the physical alphabet. Each is required to be genuinely reachable from the input prefix. No claim is made that all reachable stacks are retained.

When |B| ≥ 2, the next-to-last base color is either 1 or 2. For each i, each such color b, and each incoming color a, the table specifies a target control j and a base-length change r. The semantic audit explicitly constructs the full one-letter successors of the representative stacks `(b0) Sᵢ`. It checks that a nonempty subset of those successors can be written as B′ Sⱼ, after a permitted color relabeling, with |B′|=2+r.

It also checks r≥−1 and that B′ retains the first letter of b0. Thus the witness lifts to every longer base with the same last two colors: a single fusion step cannot touch the older prefix. This is why checking these two representatives covers arbitrarily deep bases. The witness and color permutation can be selected deterministically, for example by lexicographic order. The proof therefore defines a policy depending only on the input history; it does not look into future letters.

The verifier additionally checks that every target set is nonempty, has no duplicate suffixes, is proper, and satisfies the height and base-compatibility conditions. These checks cover all 23,129 controls, including controls that may not be reached from the initial state.

## 4. Exact negative drift under the tilted law

Let pᵢ be the integer potential divided by Q=100,000,000, and set

\[
F(B,i)=|B|+p_i.
\]

For each state and each next-to-last base color, the certificate designates one favored incoming color. Its conditional probability is 10/28; the other two probabilities are 9/28. These are probabilities of actual input letters, after undoing the stored color permutation.

For every deep-base configuration, the exact certificate proves

\[
\mathbb E[\Delta F\mid\text{past}]
\le -\delta,
\qquad \delta=\frac{3041932}{2800000000}>0,
\qquad |\Delta F|\le R=\frac{811948960}{100000000}.
\]

All expectations here use the tilted law, not the uniform law. The finite inequalities are sufficient even though the base process itself has infinitely many possible words.

When |B|<2, use a separate boundary policy. Choose one retained stack, read the next letter by any legal fusion choice, and retain only the resulting stack, encoded as the new base with control 0. Its length is at most H+2. Give the next letter the same probability multiset (10,9,9)/28, for example favoring physical color 0. This handles both the empty stack and the one-letter base without appealing to an unavailable next-to-last color. Starting from (ε,0), the retained-support invariant holds by induction at every time.

## 5. A uniform tail bound for the tilted process

Write p₋=minᵢ pᵢ. Choose θ=δ/(eR²)>0 and ρ=1−θδ/2. Then θR≤1 and 0<ρ<1. For |x|≤1,

\[
e^x\le 1+x+\tfrac e2 x^2.
\]

With V=exp(θ(F−p₋)), the drift and increment inequalities give, whenever |B|≥2,

\[
\mathbb E[V_{t+1}\mid\text{past}]\le\rho V_t.
\]

At the boundary, the next base has length at most H+2 and the next control is 0. Hence Vₜ₊₁≤D=exp(θ(H+2+p₀−p₋)). Combining the two cases gives E[Vₜ₊₁]≤ρE[Vₜ]+D. Thus E[Vₜ]≤C=V₀+D/(1−ρ) for every t.

Since F−p₋≥|B|, choose a fixed integer K with C exp(−θK)≤1/2. Then P(|Bₜ|≤K)≥1/2 uniformly in t. The constants are very conservative; this proof does not claim a useful short-word density estimate.

## 6. A positive tilted probability of winning

Set M=K+H+2. For each prefix whose base length is at most K, choose one retained stack s, of length at most K+H. Reading s in reverse pops it completely. Follow with a monochromatic word of length M−|s|≥2; that word admits a fusion computation from empty back to empty. Thus there is a suffix of exactly M letters making the original word win.

Under the tilted law, every prescribed next letter has conditional probability at least 9/28, whatever the later control states become. The selected finishing suffix therefore has conditional probability at least (9/28)ᴹ. For every n≥M,

\[
\mathbb P_{\rm tilt}(\text{length-}n\text{ word wins})
\ge c=\tfrac12(9/28)^M>0.
\]

The suffix is chosen from the prefix only. The actual retained policy need not keep that accepting branch during the suffix; existence of the genuine branch is enough to show that the word wins. This is a positive probability under the tilted law, not a positive density among uniformly chosen words.

## 7. Entropy converts the tilted law to an unweighted count

Every conditional letter distribution, including at the boundary, is a permutation of (10,9,9)/28. Its conditional entropy is therefore the fixed number

\[
h=\log28-\frac{10\log10+18\log9}{28}.
\]

For the generated letters A₁,…,Aₙ, let Iₙ=−log P(A₁,…,Aₙ). The increments of Iₙ−nh are bounded martingale differences: their conditional means are zero, and their possible values lie in an interval of length log(10/9). This does not assume independent letters.

The bounded martingale deviation inequality gives P(Iₙ<n(h−ε))→0 for every ε>0. Consequently, for all sufficiently large n, winning words with Iₙ≥n(h−ε) have total tilted probability at least c/2. Each such word has probability at most exp(−n(h−ε)). There must therefore be at least (c/2)exp(n(h−ε)) distinct winning words. Taking nth roots, a liminf, and then ε↓0 proves the displayed algebraic lower bound.

This entropy step uses neither sampled frequencies nor a claimed independence between the two counting programs. Its premises are the finite certificate, the explicit boundary policy, and the fusion-to-game soundness theorem.

## 8. Failed and exploratory approaches retained

| Approach | Observation | Defensible conclusion |
|---|---|---|
| Bounded-height regeneration, H=1,…,6 | No negative net trial drift; at H=6 a 44,488-state exact certificate proves positive drift | This particular trial/reset construction fails at those heights |
| Sliding support windows | Simulations improve strongly around H=8–10; a million-letter H=9 training run has base change −14,164 | Useful discovery data, not a population or all-state theorem |
| Small beam truncation | Smaller beams lose much of the benefit | Branch diversity matters for these tested policies |
| Uniform-input finite catalog models | All retained exact potential upper bounds are positive; H=12 best recorded value 12,345,057 / 300,000,000 | No negative uniform certificate found; does not prove that no better policy exists |
| Tilt (6,5,5)/16 | Strict exact negative drift; entropy rate about 2.988526 | Valid weaker certificate |
| Tilt (9,8,8)/25 | Strict exact negative drift; entropy rate about 2.995264 | Valid weaker certificate |
| Tilt (10,9,9)/28 | Strict exact negative drift; entropy rate about 2.996219 | Main result of this checkpoint |
| Larger H=12 model with tilt (11,10,10)/31 | Optimizer returned status 4, no certificate | Failed numerical attempt; no stronger bound inferred |

The H=6 failure receipt bounds the success probability between 3122081505617386/4503599627370496 and 3122081505617392/4503599627370496. It certifies trial drift at least 5167027224901232/4503599627370496>0. The proof uses checked subsolution inequalities and an absorbing 13-letter alternating block.

The window implementation separately passed 295,240 exhaustive prefix/window cases through length 9. These checks validate tested inputs only. They are not a substitute for the all-state semantic audit of the main certificate.

Exploration files, seeds, exact outputs, model generators, potentials and unsuccessful model tables are retained in the archive index. The ordinary drift residuals are upper bounds from particular potentials; their positivity alone is not a lower-bound certificate for the optimal policy's drift.

## 9. Reproducible audit

Download and extract `certificate-bundle.zip`. The decisive check requires Python 3 and no third-party packages:

```sh
python3 audit_certificate.py prefix9-1.txt tilted10-9.certificate.txt
python3 check_trial.py trial6-certificate.txt
python3 reproduce.py
```

The replay checks file hashes, reruns both exact audits, and validates the final constants against the preserved receipts. `python3 reproduce.py --full` additionally compiles and runs the exhaustive small-word window check. SciPy and NumPy are needed only to rerun the original numerical discovery or the older checkers.

For discovery reproduction, the complete archived table and its original uniform potential are preserved. One can run `python3 weighted_certificate.py prefix9-1.txt 10 9 replay` followed by `python3 check_weighted.py prefix9-1.txt replay.certificate.npz`. A different optimizer version may choose a different valid potential; inspect its exact inequalities rather than expecting identical bytes. Record compiler, Python, NumPy and SciPy versions and all input hashes. Never replace the preserved certificate with a new optimizer output.

Audit checklist:

1. Verify the manifest and original source commit; verify the model and text certificate hashes above.
2. Inspect the top-right/top-first convention conversion and the pinned fusion soundness theorem.
3. Recheck every control's nonemptiness, properness, height, and compatibility with its base.
4. Recheck all 138,774 subset witnesses, including the r=−1 boundary exposure and color permutations.
5. Recheck all 46,258 rational drift inequalities, the increment bound, and state 0.
6. Review the separate |B|<2 policy, the exponential tail calculation, and exact-length finishing suffix.
7. Review the entropy conversion without assuming independent letters or uniform input.
8. Keep finite checking, paper proof, imported Lean evidence, and future Lean builds separate.
9. Seek an external reviewer or an actual Lean formalization; record exact artifacts reviewed and counterexamples.
10. For any future canonical GitHub change, obtain explicit approval, perform the action, and verify its actual commit/CI receipt before marking it completed.

## 10. Remaining obligations and coordination draft

- **Exact LC004 enumeration:** find an exact tractable all-length formula or equivalent solution for the target sequences. This certificate does not discharge that obligation.
- **Uniform ternary growth:** prove growth exactly 3 or positive uniform density, or find a counterargument. The earlier length-384 expectation remains unproved.
- **Formalization:** express the finite-control soundness, boundary repair, drift-to-tail lemma, and entropy counting lemma in Lean; then compile and retain exact-source receipts. No such new compilation is reported here.
- **Independent review:** examine the finite lifting argument and the change of measure. All local work here comes from one agent.

Suggested Claude review text: “Audit R20261111C at the preserved model and text-certificate hashes. First run the standard-library checker. Then attack the arbitrary-base lifting, boundary policy, fixed-length completion, and entropy argument. Identify any false inference from tilted probability to uniform density. Return the exact artifact hashes reviewed, a counterexample if one exists, and a ranked plan for the remaining exact enumeration problem.”

This is a stored draft, not a message sent to Claude. No canonical GitHub commit, pull request, or new CI run was created by this checkpoint. The original PR52/PR53/PR54 evidence, W27/W28 agreement, previous failed approaches, and prior research import remain unchanged.
