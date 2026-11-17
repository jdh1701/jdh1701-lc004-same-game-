# Tool-grounded continuation research

## Objective and result

The objective remains the unsolved enumeration of distinct winning words over arbitrary alphabets, especially three or more colors. The verified face criterion and certificate product are structural foundations. They do not count each winning word exactly once across its potentially many certificates.

This experiment attacks a possible finite summary for the unresolved heavy-word case. It retains every color count, the complete sequence of run colors, the total number of heavy runs, and both exact boundary-run lengths. Even adding the present winning/losing status does not make that summary determine the next continuation.

Lean-certified witnesses, with A=0, B=1, C=2:

- u = AAABBABCCCBC
- v = AAABABBCCCBC

Both are losing. Each has four occurrences of each color, run-color sequence A,B,A,B,C,B,C, three heavy runs, initial run length three, and terminal run length one. Appending C makes u winning and leaves v losing. The winning executable run-index path is [1,0,1,0,0]. The original-color multiplicities and boundary summaries agree by kernel computation. RunSolvable conclusions use the existing compiled foundation; no new semantic transfer to RawMaxErases is silently asserted.

Source: research/ContinuationSummaryObstruction.lean. The audit rejects unsupported axioms. The eight audited theorem declarations are engineering coverage, not eight independent discoveries. The result establishes a concrete failure of this summary, not the impossibility of every finite or algebraic counting construction. No literature priority claim is made.

## Tools actually used

- OpenAlex: anonymous GET requests succeeded. The binary-game publication was resolved to W4403297183 and DOI 10.1080/00150517.2007.12428215. Bounded citation and title searches were archived. Neither an empty citing-work result nor an empty Kurz-title result is evidence of novelty: the known Kurz source is missed by these queries.
- SymPy 1.14.0: exact rational ranks of finite word-continuation Hankel matrices, exact determinant certificates, and a symbolic binary generating-function control. No floating-point fitting.
- Z3 4.15.3: bounded counterexample selection and optimal finite feature repair. Minimality of the selected feature count is checked separately by finite exhaustive enumeration.
- Official Lean 4 REPL: source pinned to leanprover-community/repl commit 3b27c8543a48444ffab4077f47526d91849cca3d, compatible with Lean 4.19.0. Exact source hashes are checked before bootstrap. The new proof is elaborated through the REPL; a subsequent proof reuses its environment. An intentionally false arithmetic theorem must be rejected, and its environment is not reused. Native compilation separately checks the same proof file.
- GitHub: isolated research branch, native source and axiom checks, exact-computation workflow, and reviewable evidence artifacts.

LeanDojo, Rocq, Wolfram, and external GPT/Claude API calls were not used. Their use is not implied by permission. No local Rocq or Wolfram executable, provider-specific Wolfram credential, or external GPT/Claude API key was configured. Plugin discovery returned no OpenAlex/Wolfram integration in the available directory response; OpenAlex was accessible directly. No account was created and no activation email was requested. The absence of a search match is not a claim that no plugin exists anywhere.

## Exact rank experiment and a necessary control

For all prefix and suffix words of lengths at most d, form H[u,v] = 1 if uv wins and 0 otherwise. SymPy computes rational rank. A separate modular elimination selects a square integer minor, whose exact SymPy determinant is checked to be nonzero modulo 101. The certificate retains its row and column indices.

For q=3, d=2,3,4,5, the dimensions are 13,40,121,364 and the ranks are 13,37,103,268. Any exact d-dimensional linear word recognizer factors this finite matrix into a prefix matrix and suffix matrix, so its dimension must be at least the displayed rank. These are finite computational lower bounds, not a proof of infinite rank or nonregularity.

Crucial control: binary word-Hankel ranks also grow, while the established binary LENGTH-counting generating function is rational. SymPy derives an expression with denominator degree seven from the Burns–Purcell formula and checks its coefficients against independent maximal-run BFS through length fourteen. Therefore word-recognizer complexity must not be confused with impossibility of a compact scalar counting formula. A ternary scalar recurrence or cancellation law remains a viable research direction.

## Frozen training and held-out failure

Training considers all 5,775 canonical ternary heavy patterns at length twelve. To avoid trivial isolated-color padding, the synthesis dataset keeps losing patterns in which every color occupies at least two runs and no cut separates disjoint color supports. The candidate summaries are fixed before the held-out test. One-letter continuation signatures are computed for all three colors.

Within equal-summary groups, different continuation signatures impose constraints on which ordered heaviness flags must be retained. Z3 finds a minimum of six retained positions. The recorded model chooses zero-based positions 1,2,3,4,5,8. Independent enumeration confirms that fewer cannot satisfy the training constraints.

The selected six-position model FAILS the held-out length thirteen dataset, comprising 45,045 canonical ternary heavy patterns before the same filters. An explicit counterexample is retained. This falsifies that selected repair; it does not prove that every other six-feature model fails, or that no variable-size sufficient representation exists. The held-out data are not relabeled as training success.

Selected witnesses and held-out counterexamples are checked by a separate breadth-first raw deletion search. Most membership labels originate in the existing memoized solver. The symbolic, SMT, and modular calculations consequently are not three independent mathematical proofs of the language semantics. Rank and synthesis claims remain exact computational evidence; the concrete continuation obstruction is separately Lean-certified.

## Source correction found through literature integration

The publication previously gave the binary-paper authors incorrectly as John M. Burns and Donal Purcell and omitted binary from the title. Those were errors. The journal contents, journal abstract, OpenAlex record, and OCR of the original PDF agree on Chris Burns and Benjamin Purcell, Counting the number of winning binary strings in the 1-dimensional same game. The publication bibliography and embedded database are corrected separately, preserving their Library identities. This correction changes no Lean theorem or counting result.

## Replay and assurance

Install requirements.txt into an isolated environment. Build the existing foundation, then:

    mkdir -p .lake/build/lib/lean/research
    lake env lean -o .lake/build/lib/lean/research/HeavyGreedyObstruction.olean research/HeavyGreedyObstruction.lean
    lake env lean research/ContinuationSummaryObstruction.lean
    python3 research/tool_grounded_20261029/residual_hankel.py
    python3 research/tool_grounded_20261029/summary_repair.py
    python3 research/tool_grounded_20261029/bootstrap_repl.py --directory /tmp/lc004-repl
    lake env python3 research/tool_grounded_20261029/repl_check.py --repl /tmp/lc004-repl/.lake/build/bin/repl

The existing pinned Lean executable-path shim was needed locally. Hosted replay uses normal toolchain discovery. OpenAlex metadata are frozen in the repository; routine CI does not repeatedly query the literature service or require API credentials.

## Research queue and honest progress accounting

Six major milestones in this geometric phase are now available locally: geometric locality, structural Face equivalence, exact certificate assembly bijection, certificate product, heavy-preserving greedy obstruction, and the present continuation-summary obstruction. Earlier second-diagonal work is additional. This is a grouping of completed objectives, not a novelty count or a percentage of the open problem.

At least three substantial research targets remain: certify the ordered-slot correspondence; connect it to a duplication-free profile enumeration; discover and certify a non-circular general counting law for the heavy case. The last target has no known fixed number of steps and may require several new ideas.

Next discriminating experiment: search for scalar aggregation or signed cancellation identities that can be valid even when word-language state dimension grows. Preserve the full ordered heaviness pattern as a safe baseline. Any compressed proposal must reproduce the verified ternary collision and survive a freshly frozen held-out length before promotion.

Primary source links: journal record https://www.fq.math.ca/Abstracts/45-3/burns.pdf; original paper https://www.fq.math.ca/Papers1/45-3/burns.pdf; Carlyle and Paz, Realizations by stochastic finite automata, https://www.sciencedirect.com/science/article/pii/S0022000071800053; official REPL https://github.com/leanprover-community/repl/tree/3b27c8543a48444ffab4077f47526d91849cca3d. The bibliographic correction is independently supported by the journal record and the original title-page OCR, rather than by OpenAlex alone.
