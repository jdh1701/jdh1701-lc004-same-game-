# Cross-domain campaign: RNA topology, parsing, and information loss

Baseline: proof/noncrossing-components-20261029 at 0fb784ad778b0efe5f46260a24690c9b524b0f19.
The original-game connected-weight expansion already passes Lean. This pass
investigates effective enumeration; no new Lean theorem is claimed.

## Sources and transfer limits

1. Han, Li, Reidys, Combinatorics of gamma-structures (2014),
https://arxiv.org/html/1112.4151v2 ; DOI 10.1089/cmb.2013.0128.
Read the introduction and shadow definitions: fixed-genus irreducible RNA
shadows form finite families, and inflation produces generating functions.
Transfer proposal: retain a finite ordered crossing core plus local decorations.
RNA matchings and our pair/triple partition joins are different objects;
their shadow bounds and inflation equations cannot be applied without a
weight-preserving correspondence. Genus here is an explicitly defined partition
permutation statistic, not an assertion of such a correspondence.
OpenAlex exact DOI lookup succeeded (openalex.json). No novelty conclusion.

2. Goodman, Semiring Parsing (1999), https://aclanthology.org/J99-4004.pdf.
Read abstract/introduction: parser evaluation can use different semirings for
recognition, derivation forests and probabilistic inside values. Application:
retain certificate identities in an idempotent set-valued chart, then apply
signed join aggregation; integer inside counts alone count witnesses.
Our repo already explored canonical parsing and residual automata on Oct 28.
Do not repeat those as new discoveries. Compression must occur before full
word enumeration and must preserve distinct-word semantics.

3. Okhotin, Boolean grammars (2004), DOI 10.1016/j.ic.2004.03.006;
https://research.cs.queensu.ca/TechReports/Reports/2004-478.pdf.
Abstract-level lead: conjunction/complement may encode exclusion of earlier
valid parses. Recognition results do not imply efficient length enumeration.

4. Flajolet, Analytic models and ambiguity of context-free languages (1987),
https://www.cs.umd.edu/~gasarch/BLOGPAPERS/ambcfl.pdf.
Read abstract/introduction: analytic/transcendence arguments can obstruct
unambiguous grammars. We have no such obstruction proved for this game.
Finite coefficient fitting or ambiguous existing grammars cannot prove it.

5. Viennot, Heaps of pieces (1985/1986), author exposition:
https://www.viennot.org/abjc2.html ; original-paper lead:
https://curien.galene.org/Damien/LNM-1234-Joyal.pdf.
Search-level lead only: dependence/commutation structures and alternating
inversion may describe overlapping certificates. Need a game-specific bijection;
naive pairwise crossing graphs already lose the coefficient information below.

## Exact experiments and statuses

VERIFIED-COMP: all 121 connected partitions of type (5,5), n=10: 116 zero,
5 coefficient -1. All 451 connected partitions of type (5,6), n=11: 429 zero,
22 coefficient -1. Coefficients computed by partition-lattice Mobius inversion
of a raw maximal-run solver, independently crosschecked by signed certificate
join aggregation (572 cases). Full witnesses and scripts retained.

KILLED: coefficient depends only on class sizes and crossing graph.
KILLED: coefficient depends only on class sizes and the tested genus statistic.
Counterexamples are explicit in results.json and results56.json; all have two
crossing classes. These do not kill decorated shadows or full ribbon structures.

The conditional entropies in the JSON are empirical information-loss diagnostics
under the uniform distribution on the enumerated family. They are not sampling
p-values, generalization bounds, or statistical proofs. Exact collisions, not
entropy magnitudes, refute the proposed sufficient summaries.

In these first two families certificate count has zero conditional coefficient
entropy. This is only a narrow computational observation. probe57.py is a seeded
holdout from 80 type-(5,7) partitions at n=12, excluding nonconnected samples.
Consult results57sample.json for the actual outcome; do not promote the earlier
observation to a theorem. Selection was fixed before inspecting those results.

## Concrete next approach / Claude handoff

Prioritize certificate-overlap structure with ordered endpoint decorations.
Try reducing its join poset or simplicial complex using discrete Morse matching,
while preserving the alternating sum; the prior universal redundant-atom cone
attempt has already failed, so a single globally redundant certificate is too
strong. A successful state compression must prove equal signed weight on every
fiber, then support insertion/deletion transitions without enumerating all words.

RNA shadows supply a design pattern for finite cores, not a ready-made formula.
Use held-out class profiles and exact collision tests before formalizing a
proposed compressed invariant. Pass Claude the collision witnesses and ask for
a weight-preserving decorated-core construction or an explicit counterexample.
No direct Claude API was used. No new Lean or Sage pass is claimed here.

## Held-out outcome

VERIFIED-COMP: the seeded (5,7) holdout retained 79 connected patterns; 75
coefficients were zero, one was -1, and three were +2. Signed-join crosschecks
also passed, bringing the independent comparison to 651 patterns.
Certificate count still separated coefficient values within this small holdout;
this is not sufficient evidence for a general rule. Certificate count alone
across profiles is KILLED: count 7 gives coefficient 0 in (5,6) and +2 in (5,7).
The positive coefficients also rule out a universal nonpositive sign rule for
two-class connected kernels; they do not refute the special all-five conjecture.

The next decisive test is same class profile AND same certificate count with
unequal coefficients, followed by a test of the full overlap signature. No
probabilistic model should be trained on these few profiles and presented as a
proof. The permutation genus statistic remains a useful stratifier, although
it is not sufficient for exact coefficients.
