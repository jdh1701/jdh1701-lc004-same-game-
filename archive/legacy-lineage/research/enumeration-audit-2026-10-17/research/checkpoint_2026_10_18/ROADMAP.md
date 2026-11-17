# Same Game enumeration: remaining proof obligations

Checkpoint: 2026-10-18. Initial base: `7fe93b8d01742104ef0479f3e0988db532fef644`.
Updated by the [raw/grammar and connected-coefficient checkpoint](bridge/STATUS.md),
whose base is `c04443b029ff85da4fad7ecc65f2d6e29f9aabb2`.
The subsequent [factorization checkpoint](factorization/STATUS.md) adds formal
coefficient and witness-decomposition lemmas and tests lengths 14 and 15.
The [cancellation checkpoint](cancellation/STATUS.md) develops the four-gap
mechanism, proves its conditional coefficient machinery, and tests the exact
small-block formula and its failure at size five.
The [four-gap witness checkpoint](gaps/STATUS.md) constructs regional witnesses,
discharges the corresponding intersection-invariance condition, and proves
regional four-position cancellation at arbitrary ordered board positions.
The [transport checkpoint](transport/STATUS.md) proves coefficient locality,
the disjoint-part partition product isomorphism and full-board coefficient
transport. Its [novelty audit](transport/NOVELTY_AUDIT.md) records that the
length-12–15 polynomials already appear in OEIS A323844. Those numerical
results are reproductions; the cancellation law's originality is unestablished.
The [complete-family checkpoint](coverage/STATUS.md) now proves exact
witness-family identification and four-position cancellation for all
pair/triple witnesses. No coverage premise remains. Stage F is now partial;
no additional major stage has been declared complete.

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
| F | A useful general recurrence or structural coefficient description, with a growth analysis | **Partial**: unconditional four-position cancellation for all witnesses is proved; remaining connected coefficients and growth analysis open | The substantive enumeration result; generic inclusion-exclusion alone is insufficient evidence of solving it |
| G | End-to-end theorem equating the proposed formula with W(q,n), and novelty assessment | **Open**, depends on B, C2, E2/F | A defensible final solution claim |

The semantic and executable Lean obligations B and C2 remain necessary.
The complete four-position witness coverage proof is now closed. The
immediate structural priority is size-two/three and component assembly;
the mathematical priority is F, using the exact
coefficient map as a falsification tool. Do not assume
that coefficients depend only on block counts or that joins stay noncrossing.

There are **9 major stages: 4 verified, 2 partial, 3 open**. They have unequal
difficulty; this count is not a percentage estimate of progress to a solution.
The complete-family checkpoint adds 31 named Lean theorems, including helpers,
and moves F to partial without closing another whole stage. Current
machine-readable statuses are in `coverage/STAGES.json`; the historical
`bridge/STAGES.json` is preserved for its original audits.

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
values. This was an internal prediction: the subsequent novelty audit found
the polynomial already listed in OEIS. It establishes no public priority
or externally blinded holdout. Neither candidate is yet a general theorem. The simpler linear
connected-weight model was falsified at length 10. See `bridge/STATUS.md` for
the exact hypotheses, evidence, and next proof obligations.

Factorization now has an explicit mathematical argument and Lean proofs of
its algebraic and witness-decomposition ingredients. The transport checkpoint
now supplies a two-part partition-ideal product isomorphism and coefficient
transport. Assembly across all noncrossing-closure components and generator
identification remain formal obligations. F is now partial because of the
complete-family four-position theorem, not because factorization is complete. See
`factorization/FACTORIZATION_ARGUMENT.md` for that boundary.

The minimum-five support condition now has a proposed cyclic-gap cancellation
argument in `cancellation/ARGUMENT.md`. Its algebraic two-branch theorem and
chord-separation lemma are compiled in Lean. The actual forced-pairing/gap
invariance is now proved for the complete specified regional witness families
in `FourGapWitnesses.lean` and `RegionalCancellation.lean`. Identification with
the entire full-board witness family and exhaustive branch classification
are now proved in `AllWitnessCancellation.lean` and
`QuadWitnessClassification.lean`. Combined with locality and coefficient
transport, `all_witness_four_block_zero` proves cancellation for every
length with no assumed coverage premise. The general minimum-five theorem
must still not be counted as Lean verified: the size-two/three and component
assembly obligations remain. This advances F to partial while the number
of fully completed major stages remains four.

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
