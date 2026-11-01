# Global Boolean fusion route (2026-11-01)

Status: research toward LC004/A035617, **not a solution of the open enumeration problem**. The Lean bridge and exact residual-language theorem passed the full build, declaration axiom audit and negative guards at source 66acdf532a39a7759bcf80576fa30610438a8881, run 41328980684. See the final verification receipt for the complete source and checks.

## Exact global model

Store a proper stack with its top at the right. Reading a color a sends a stack s to {s, s without its last letter} if its top is a, and to {sa} otherwise. Apply this to a set of stacks by union, starting at {empty}. A word wins the original maximal-run game iff the final set contains the empty stack.

Completeness: inserting aa or aaa anywhere in a word preserves each existing stack computation: when the top is a, stay twice or three times; otherwise push/pop or push/stay/pop. The previously proved equivalence of maximal-run winning with auxiliary pair/triple erasure therefore gives an accepting computation for every winning word.

Soundness: induct on a stack computation, maintaining that reverse(initial stack) followed by the unread word wins whenever reverse(final stack) wins. A push leaves this word unchanged. A pop inserts a monochromatic pair. A stay duplicates one occurrence, which preserves winning by the proved run-inflation theorem. Thus this uses the actual game, not an assumption that singleton deletion is legal. Lean uses top-first lists and formalizes both directions in LC004/FusionStack.lean.

## Counting distinct words

At depth k of a target length N, retain the distribution of support sets, discarding stacks longer than N-k. One letter can pop at most once, so discarded stacks cannot accept any remaining suffix. For each color, apply the transition and add the prefix multiplicity to the successor set. Canonicalize whole sets by a common permutation of the alphabet; equivalent successor sets still receive one contribution for every input color. At depth N sum weights on sets containing empty. This is an exact finite recurrence for every N, but its state distribution is unbounded and has not yielded a scalar counting formula.

The C++ executable implements ternary counts with checked uint64 arithmetic, a state cap, and an explicit N <= 40 encoding bound. These implementation limits are not mathematical bounds on the recurrence. Python independently implements the same recurrence using tuples and sets. Neither algorithm uses the certificate catalogue.

## A precise obstruction to compressing the boundary

For proper words s,t, a stack s accepts the proper suffix reverse(t) iff s=t. Every accepting step must pop: a first push or stay forces the remaining proper letters to push, leaving a nonempty stack. Hence every two distinct support sets have different future languages, distinguished by reverse(t) for a stack in their symmetric difference. The same conclusion holds for truncated supports and suffixes of length *at most* the horizon; it is not a claim of minimality for suffixes of exactly the horizon.

For b colors and proper words of length m, the matrix H(s,reverse(t)) is the identity of order b(b-1)^(m-1). Its rank over every field is that order. This rules out a polynomial-dimensional exact linear representation of all word boundaries. It does not rule out an algebraic scalar length generating function, or a way of summing many residual states without enumerating them. The observation strengthens the earlier identity-submatrix obstruction, rather than constituting a solution.

## Algebraic route and rejected shortcuts

Over positive coefficients, the letter operators satisfy X_a^2 = I + X_a. The coefficient of the empty stack is positive exactly on winning words. Coefficients count fusion paths, not distinct words or necessarily original deletion histories: AAAA has coefficient 2 although its indicator is 1. Changing the stay weight to any positive number keeps the same support and does not solve this multiplicity problem.

The sum of these multiplicities has the algebraic generating function M(z)=1/(1-b z^2 F(z)), where F=1+zF+(b-1)z^2F^2. It is an upper bound, not the answer to A035617. A positive weighted row bound gives M_n <= (1+2 sqrt(b-1))^n for b>=2, so this bound implies exponential decay of winning density for b>=6, but not for three colors.

Three binary projections do not determine the ternary indicator. The word 010012002 loses while deleting any one color gives a winning binary word. Exhaustive search finds the first lexicographic length-nine counterexample 001020021, and none shorter. Proper prefixes ABA and ABC have the same length and different winning continuation counts at suffix length seven (131 versus 132); depth alone cannot replace a support state.

## Evidence and limitations

check.py exhaustively compares the support against the original maximal-run solver on binary words through length 12, ternary words through length 10, and four-color words through length 7 (118,609 original-word replays). It also checks the split intersection criterion, proper-suffix separators, positive-parameter support, identity boundary matrices, Python/C++ state distributions through N=14 and counts through N=18. The machine-readable receipt is checks.json.

Separate local C++ runs reproduce W_24=46,435,889,601 and W_25=141,985,777,503, both already published OEIS terms. N=25 peaks at 3,216,015 support states and took about 141 seconds / 2,076,268 KiB maximum resident memory on this machine. This growth is a real unresolved obstacle, not evidence of a finished formula.

Prior literature already gives a context-free recognition algorithm: Biedl et al., The Complexity of Clickomania, arXiv:cs/0107031. No novelty is claimed for context-free recognizability. The free-product fusion viewpoint is a candidate organizing tool, not a cited solution of the counting problem.

## Repository reconciliation

PR35 advanced from c88cc09 to e51bbcb by a WORKBOARD review, without new proof sources. That review overstates PR51 by omitting its universal-certificate hypothesis: nonzero (7,5,...) classes without a universal certificate need not be singleton triplings. PR50's +1 witness already contradicts the overstatement. The present work preserves the hypothesis and does not count a documentation review as an independent proof check.

## Further attack: run-normalized majorant

RUN_BOUND.md derives an algebraic series that removes redundant choices inside each original maximal run. Its coefficients still overcount winning words, with a first ternary discrepancy at length six. It gives the explicit paper bound W_5(n)/5^n <= 129 (40/41)^n, hence exponential density decay for every alphabet size at least five. This does not resolve b=3 or b=4. The proof and exact finite checks are separate from the Lean semantic bridge.

The C++ recurrence also computes W_26=434,087,233,947, beyond the term range displayed in A035617 on November 1, 2026. The independent half-word incidence replay described below now agrees exactly.

## Independent half-word incidence count

Each color's fusion transition matrix is symmetric on proper stacks: a push and its reverse pop have the same color, and a stay is a loop. Therefore a path reading v from stack s to empty exists iff a path reading reverse(v) from empty to s exists. Splitting a word uv gives

    wins(uv) iff support(u) intersects support(reverse(v)).

For fixed half lengths l+r=N, reversal permutes all r-letter words. Thus the total winning count equals the number of pairs (u,t), |u|=l, |t|=r, whose supports intersect.

fusion_meet.cpp explicitly enumerates every right half-word, recording for each stack the set of half-word IDs that reach it. It separately records the multiplicity of each left support orbit under global color permutations. For a left support S, the union of its stack postings is exactly the right words intersecting S; its cardinality times the left multiplicity contributes to the total. The right universe contains all labeled words, so global color permutations of a left support preserve this cardinality. Sparse lists and dense bit vectors only change how this union is computed.

This implementation uses top-first strings, explicit half-word enumeration, and incidence unions. It shares neither the forward program's bit-encoded stack representation nor its horizon pruning or state-distribution recurrence. It independently reproduces every count through length 26. In particular W_26=434,087,233,947 agrees between both methods; the independent replay takes about 31 seconds and peaks at 385,956 KiB for the batch through N=26.

The half-word computation further gives W_27=1,326,879,233,787 and W_28=4,055,050,431,933 (counts27-28.json). These two terms have this one algorithmic replay, unlike W_26's two-method agreement. The runs took about 86 and 200 seconds; the batch peaked at 2,070,404 KiB. No OEIS submission has been made.

RUN_BOUND.md also supplies a separate elementary argument using blocks of three: W_5(n)/5^n <= (24/25)^floor(n/3). It avoids analytic continuation and independently confirms five-color exponential decay. These bounds are paper proofs, not Lean theorems.

## Small scalar-formula attacks, with held-out terms

scalar_search.py uses exact rational Gaussian elimination. It fits the old coefficients through N=25 and tests the new N=26..28 terms, keeping the *entire* training nullspace rather than testing only individual basis vectors. No nonzero homogeneous recurrence of order at most 13/9/6/5/4 and coefficient degree at most 0/1/2/3/4, respectively, survives when required from n=0. It also excludes polynomial equations P(z,W(z))=0 with degree bounds (degree in W, degree in z) equal to (1,13), (2,8), (3,6), (4,4), or (5,3). Several templates fit the old terms and fail the new ones. These are finite exclusions of specified templates, not proofs that the sequence is nonalgebraic or non-D-finite, and not exclusions of recurrences that start later.
