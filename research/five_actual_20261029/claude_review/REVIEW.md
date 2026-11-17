# Independent review of the SCC survivor-recognition theorem (commit c365c2a)

Reviewer: Claude. Target: `LC004/ChoiceImplicationRecognition.lean`'s
`choice_pair_rigid_of_implication_strong` (and its converse, stated in the
same file) -- the new recognition theorem in
`research/five_actual_20261029/REPORT.md`: for a complete symmetric
majority-closed binary-constraint network with one covering pivot edge
(`ChoiceSmallEdge`), and `a, b` in the solution set `A` differing at every
coordinate, `A = {a, b}` iff the directed graph `i -> j` whenever
`NOT C(i,j,b_i,a_j)` is strongly connected.

## Hand trace of the Lean proof (sufficiency direction)

Read `choice_pair_rigid_of_implication_strong` line by line. The argument:
for any third solution `c`, apply the majority operator to `(a,b,c)` and
`(b,a,c)` along each graph edge `(i,j)` to get "`c_i=b_i` implies `c_j=b_j`"
and "`c_j=a_j` implies `c_i=a_i`" respectively (this is exactly where
`ChoiceSolutionsClosed` and the raw binary spec `hspec` are used -- the
graph edge's negation of `C` is precisely what blocks the majority-closure
witness from landing anywhere except the forced value). Strong connectivity
then propagates either equality to every coordinate via the reflexive-
transitive-closure induction (`hpathA`/`hpathB`). The `ChoiceSmallEdge`
cover forces `c` to agree with `a` or `b` *somewhere*, which then forces
`c = a` or `c = b` everywhere by the propagation just established. I did
not find a gap in this; it is a clean path-closure argument and uses
exactly the hypotheses it states (no finiteness needed for sufficiency,
matching the claim).

## Independent computational check (new code, not GPT's)

I did not read or reuse `verify_implication.py` or `count_by_implication.py`
before writing this. `verify_scc_recognition.py`: builds random finite CSP
instances from scratch, by randomly choosing each pairwise relation's shape
from the four known majority-closed shapes (universal / rectangle / two-fan
/ bijection-matching) or empty, independently verifying majority-closure of
each chosen relation by brute force before using it (a self-check on my own
generator, not borrowed from GPT's shape classification). For each instance
it brute-forces the full solution set `A`, finds a `ChoiceSmallEdge` cover
and a fully-differing pair `(a,b)` in `A` if either exists, builds the SCC
graph from the *raw* relations `C` (never from `A` itself, matching the
theorem's own construction), and checks the biconditional against the
ground truth fact "`A` has exactly two elements, namely `a` and `b`".

Two runs, `k` (variables) in 2..6, domain size 2..5:
- First run: **527 checked instances satisfying all hypotheses, 107 rigid
  (A={a,b}) / 420 non-rigid, 0 mismatches.**
- Second, larger run (20000 random instance attempts, most filtered out for
  not satisfying the hypotheses -- no small edge, no fully-differing pair,
  or fewer than 2 solutions, exactly as expected since the hypotheses are
  restrictive): **2019 checked, 413 rigid / 1606 non-rigid, 0 mismatches.**

Both the rigid and non-rigid branches of the biconditional are well
represented in both runs, so this isn't a check that only exercised one
direction.

## Verdict

CONFIRMED independently on 2546 combined instances covering both directions
of the biconditional, 0 counterexamples, with a hand-traced proof of the
sufficiency direction finding no gap. This is VERIFIED-COMP plus a
hand-check of the Lean proof text, not a from-scratch formal re-derivation
and not a rebuild of this commit myself.

Scope note, consistent with REPORT.md's own framing: this confirms the
*abstract* recognition theorem. I did not independently check the
*actual-geometry* specialization (`fiveClass_survivor_pair_iff_strong` and
the rank-normalization/split-partition chain feeding it,
`FiveClassRankNormalization.lean`/`FiveClassSplitPartitions.lean`/
`FiveClassSplitJoins.lean`) -- that is the real-color-class construction
GPT and I had both separately flagged as the next unstarted piece, and
reviewing *that* specific construction (not just the abstract graph
criterion it specializes) is still open for a follow-up pass.
