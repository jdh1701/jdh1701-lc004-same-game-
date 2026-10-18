# Same Game enumeration: remaining proof obligations

Checkpoint: 2026-10-18. Initial base: `7fe93b8d01742104ef0479f3e0988db532fef644`.
Updated by the [raw/grammar and connected-coefficient checkpoint](bridge/STATUS.md),
whose base is `c04443b029ff85da4fad7ecc65f2d6e29f9aabb2`.
The subsequent [factorization checkpoint](factorization/STATUS.md) adds formal
coefficient and witness-decomposition lemmas and tests lengths 14 and 15.

The target is W(q,n), the number of length-n words over q labelled colours
that can be completely removed by legal maximal-run deletions. Count each
word once. Unique-path enumeration is a separate problem. This checkpoint
does not claim to solve the unresolved general enumeration problem.

## What changed in the strategy

The raw/run semantic bridge is already closed. Further small ambiguity
certificates are useful diagnostics but do not directly count all winning
words. The current priority is therefore the overlap between structural
witnesses of solvability.

Biedl et al.'s grammar has productions epsilon, SS, cSc, and cScSc.
Decomposing by the block containing the first position gives noncrossing
pair/triple witnesses. One word can satisfy several witnesses. Assignments
of colours to different witness blocks are allowed to coincide.

We now have a Lean proof of the algebra that corrects those overlaps, a
Lean proof that an equality partition with b blocks has q^b compatible
colourings, and an independent Python implementation of the corresponding
partition-join computation. Connecting the generated witnesses to the
existing raw game in Lean remains necessary.

## Dependency map

| Stage | Required result | Status | What it unlocks |
|---|---|---|---|
| A | Raw maximal-run deletion commutes with encoding; successful paths correspond | Proved previously, `OrdinaryFinal.lean` | A stable formal game specification |
| B | Raw solvability iff the published grammar | **Partial**: `ordinarySolvable_clickGrammar` proves raw-solvable implies grammar; converse open | Transfers grammar counting to the actual game |
| C1 | Published grammar iff leftmost pair/triple block decomposition | **Proved now**, `clickGrammar_iff_firstBlock` | Removes associative concatenation parses |
| C2 | A finite generator of equality partitions recognizes exactly C1 at each length | Python generator checked; **Lean proof open** | A concrete finite witness family without a game-solving oracle |
| D | Equality-event intersections are joins; each event has q^b words | **Proved now**, `respects_join`, `card_partitionEvent` | Correct intersection weights for arbitrary q and n |
| E1 | Signed union identity counts every covered word exactly once | **Proved now**, `partition_union_count` | General overlap-correct counting for any supplied partition list |
| E2 | Collecting equal joins in the executable coefficient map preserves E1 | Implemented and tested in Python; **Lean refinement open** | A verified compressed executable instead of exponential term-list expansion |
| F | A useful general recurrence or structural coefficient description, with a growth analysis | **Research open** | The substantive enumeration result; generic inclusion-exclusion alone is insufficient evidence of solving it |
| G | End-to-end theorem equating the proposed formula with W(q,n), and novelty assessment | **Open**, depends on B, C2, E2/F | A defensible final solution claim |

The next Lean priority is B and C2. The next mathematical priority is F,
using the exact coefficient map as a falsification tool. Do not assume
that coefficients depend only on block counts or that joins stay noncrossing.

There are **9 major stages: 4 verified, 1 partial, 4 open**. They have unequal
difficulty; this count is not a percentage estimate of progress to a solution.
The new bridge adds 12 named Lean theorems, including helpers, without closing
another whole stage. Machine-readable statuses are in `bridge/STAGES.json`.

## Immediate next proofs

1. **Completed in the bridge checkpoint:** insertion closure of `ClickGrammar`,
   monochromatic words of length at least two, and decomposition of actual
   raw deletions prove raw-solvable implies grammar membership.
2. Formalize the converse without silently permitting partial deletion
   of a maximal run. A suitable intermediate statement is an internal
   solution lemma: boundary runs can be postponed, allowing concatenation
   and pair/triple enclosure. This is the subtle semantic direction.
3. Represent a first-block witness with fresh labels for its disjoint
   subintervals. Prove generator soundness and completeness by length
   induction, then convert its equality relation to `Setoid (Fin n)`.
4. Relate the dictionary update to the signed-list specification by
   summing coefficients for equal partition keys; prove zero cancellation
   and order independence. Prove the union-find join implementation agrees
   with supremum of equivalence relations.
5. Search for a recursive description of the **signed** join support.
   Validate predictions against existing full polynomials and held-out
   lengths before attempting a general theorem. A finite fit is not a proof.

The current structural candidates are factorization over the blocks of the
noncrossing closure, and cancellation of nontrivial connected terms containing
a block of fewer than five positions. Together they predicted the entire
length-13 polynomial before the new join calculation. That prediction passed;
independent maximal-run enumeration also confirmed its three- and four-colour
values. Neither candidate is yet a general theorem. The simpler linear
connected-weight model was falsified at length 10. See `bridge/STATUS.md` for
the exact hypotheses, evidence, and next proof obligations.

Factorization now has an explicit mathematical argument and Lean proofs of
its algebraic and witness-decomposition ingredients. The partition-ideal
product isomorphism, coefficient transport, and generator identification
remain formal assembly obligations. Therefore F is still open and the fixed
stage count remains 4 verified, 1 partial, 4 open. See
`factorization/FACTORIZATION_ARGUMENT.md` for that boundary.

## A shortcut ruled out now

Two noncrossing pairings on eight positions have label words

```
01102332
01233210
```

Their join in all equivalence relations has labels `01100110`. Its two
blocks cross: positions 0 < 1 < 3 < 5 lie alternately in them. Both input
partitions are noncrossing, proved in Lean, and the join crosses, also
proved in Lean. The inputs are generated by the pair-only grammar.

The two-event union has size 2q^4-q^2. Replacing its intersection by the
noncrossing closure gives 2q^4-q, which is wrong: 28 versus 30 for q=2,
and 153 versus 159 for q=3. These numerical union counts are independently
checked in Python; the Lean certificate establishes the structural
crossing counterexample, not those concrete cardinalities.

In the full witness union, crossing terms happen to cancel through n=9.
At n=10, five crossing partitions survive, each with coefficient -1.
That last assertion is finite Python evidence, not a universal Lean theorem.

## The independent ambiguity-family question

The proposed alternating 010/212 family still has only finite verification:
the earlier five- and six-way examples are formal theorems, while the
parameterized 2k-way minimality claim is unproved. A general proof would
rule out bounded interaction arity for that uniqueness model. It would
not by itself enumerate W(q,n). Keep this as a separate structural target.

## What qualifies as completion

An end-to-end kernel-checked theorem must use the actual raw game,
specify the alphabet and empty-word cases, count words once, and state
all hypotheses. The proposed general counting method needs a clear
mathematical advantage over direct exhaustive enumeration and an honest
comparison with prior work. No finite census, fitted recurrence, conditional
bridge, or formula that calls an unanalysed winning-word oracle closes
those obligations.
