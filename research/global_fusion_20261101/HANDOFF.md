# Handoff: global Boolean fusion route

The full LC004/A035617 enumeration problem remains open in this work. Do not describe the exact recognition model, finite recurrence, or sequence extension as a closed counting solution.

## Exact source and formal results

Verified source: 293cdb9766aa386963f59e33db54d43c48317171, tree bd425c7d3e0019dd5ea53816771343f219680f9f, GitHub Actions run 41329698273. Both jobs passed. All 250 active modules build; the axiom audit covers 4266 project declarations and permits only propext, Classical.choice and Quot.sound. Source, negative coverage and negative axiom guards passed; the pinned manifest remained unchanged.

LC004/FusionStack.lean proves, for every finite alphabet and every word:

- Original maximal-run winning iff empty belongs to the executable Boolean fusion support.
- A proper suffix accepts exactly its corresponding stack.
- Equal support sets iff identical winning continuation languages.
- Reversal of a computation on proper stacks.
- wins(u ++ v) iff support(u) intersects support(reverse(v)).

The final item is the all-length mathematical basis for half-word counting. These are theorems about the original game, not a conditional grammar bridge. They do not themselves formally verify the C++ implementations.

## Counts

W_26 = 434087233947, W_27 = 1326879233787, W_28 = 4055050431933.

The forward support-distribution DP and the separately implemented half-word incidence method agree through N=26. The half-word method computed N=27,28 locally and reproduced them in hosted CI. These last two terms have one counting algorithm, not two independent methods. The OEIS A035617 page checked on November 1, 2026 listed only N=0..25. No public sequence submission was made.

The forward N=26 run took 362 seconds and 5.16 million KiB maximum RSS; the half-word N=26 replay took 31 seconds and the batch through N=26 peaked at 386 thousand KiB. Half-word N=27 and N=28 took 86 and 200 seconds; their batch peaked at 2.07 million KiB. Performance is machine-specific and is not an asymptotic complexity claim.

## Paper results and rejected closures

RUN_BOUND.md derives a run-normalized algebraic *majorant*, with two proofs of exponential decay for five-color winning density:

    W_5(n)/5^n <= 129 (40/41)^n,
    W_5(n)/5^n <= (24/25)^floor(n/3).

The second proof uses only a nonnegative triple-block operator and avoids analytic continuation. Ordinary fusion multiplicity already handles b>=6. These paper proofs are not Lean formalized, are not three-color enumeration formulas, and carry no claim of historical novelty.

Rejected routes are documented with explicit witnesses: recovering ternary winning from its binary projections; replacing fusion by ordinary involutions; keeping stack depth alone; using fusion path multiplicity as a word indicator; and using capped-run multiplicity as a word indicator. The proper-prefix boundary matrix has exponential rank, but this does not exclude an algebraic scalar length generating function.

Exact rational searches exclude 37 specified polynomial-coefficient recurrence templates from n=0 and five bounded algebraic generating-function templates. Several fitted all old terms and failed the held-out N=26..28 terms. This is not a non-D-finiteness proof and does not exclude later-starting recurrences.

## What remains

A way to count distinct winning words globally without enumerating an expanding distribution of supports, or an equivalent proven scalar formula, remains missing. Existing certificate-profile work remains valid but incomplete for arbitrary profiles. Do not infer general impossibility from the residual-language theorem: averaging over all future words is a weaker requirement than preserving each future word separately.

PR35's documentation review omitted the universal-certificate hypothesis in its summary of PR51. That omission is false: PR50 already contains a +1 non-universal seven-class witness. Preserve PR51's hypothesis; no new proof source arrived in that review.

PR52 is stacked on PR51. The receipt-only commit after the tested source adds documentation and archived verification evidence; receipts.json identifies the exact tested commit. The archive retains the two failed elaboration attempts as well as successful full logs. No local Lean installation was available; formal checks were hosted.
