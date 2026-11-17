# Partition counting checkpoint

Date: 2026-10-18. This is verified progress toward general winning-word
enumeration, not a claim that the open enumeration problem is solved.
See [ROADMAP.md](ROADMAP.md) for the ordered remaining obligations.

**Later checkpoint on the same date:** [bridge/STATUS.md](bridge/STATUS.md)
records the newly proved raw-solvable-to-grammar direction, the fixed nine-stage
count, a prospective length-13 prediction, and independent raw-game checks.
The body below records the earlier partition-counting checkpoint; its statements
about the then-open semantic bridge are historical.

## New Lean results

- `GrammarNormalForm.lean`: `ClickGrammar` is exactly the published
  epsilon/concatenation/pair/triple grammar. `clickGrammar_iff_firstBlock`
  proves an equivalent leftmost-block decomposition. `clickGrammar_map`
  allows arbitrary colour maps, including identification of colours.
  Neither theorem yet transfers to the raw game in this repository.
- `SignedConstraints.lean`: a signed term list updates by old + new -
  intersection. `signedEval_unionTerms` proves, for all objects and all
  witness lists, that its value is 1 exactly on the covered objects and
  0 elsewhere, assuming the stated conjunction law for intersections.
  `signed_constraint_count` sums this identity over an arbitrary finite
  domain. This is standard inclusion-exclusion algebra, not a novelty claim.
- `PartitionCounting.lean`: concrete equality constraints are setoids
  on `Fin n`; the conjunction law is discharged by the lattice join.
  `card_partitionEvent` proves q^b compatible colourings, using the
  equivalence with functions from the quotient. `partition_union_count`
  is an unconditional signed-union counting theorem for any finite list
  of such partitions, any n and any q, including zero.
- `CrossingJoin.lean`: two explicit noncrossing pairings have a crossing
  join. Both noncrossing checks and the crossing conclusion are proved.
  This prevents an incorrect restriction to the noncrossing partition
  lattice when evaluating intersections.

The new declarations use only the standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`, or subsets. There are no proof holes,
project-specific axioms, native decision proofs, or overridden evaluators.

## Exact counting construction

For an equality partition p, let E(p) be the words constant on its blocks.
The allowed equalities do not require different blocks to have different
colours. Thus |E(p)|=q^b(p), and E(p) intersect E(r)=E(p join r).

Starting with no terms, insert each witness p by:

1. retaining the old coefficient map a;
2. adding +1 at p;
3. adding -a(r) at r join p for every old term r;
4. collecting equal keys and removing zero coefficients.

For the resulting map, the candidate winning-word count is
`sum_r a(r) * q^(number_of_blocks(r))`.
The universal signed-list counting identity and the partition weights are
Lean theorems. The Python fresh-label generator, union-find, and dictionary
compression are not yet a verified refinement of those Lean definitions.
The grammar-to-game and generator completeness bridges are explicitly open.

The algorithm does not enumerate q^n labelled words and its partition work
is independent of q. However, it still enumerates exponentially many
structural witnesses and may have large join support. No efficient general
recurrence, asymptotic theorem, or priority claim is made here.

## Executed evidence

`partition_count.py --max-n 12 --word-check-n 8` completed with zero failures.

- All 5,296 equality types through length 8: witness union, signed indicator,
  the independent grammar recognizer, and the direct raw deletion solver
  agree pointwise.
- At every length 0 through 12 and q=0 through 8: the polynomial agrees
  with the existing independently enumerated raw/run orbit coefficients
  (117 alphabet evaluations). Degree is at most floor(n/2), so these
  evaluations also determine the compared polynomials exactly in this range.
- At n=12: 1,177 pair/triple witnesses combine to 4,351 nonzero signed
  partition terms; the q=3 count is 71,385. The measured local computation
  took about 21 seconds for this length. This is not a general complexity bound.
- `join_controls.py` checks the eight-position wrong-lattice example by
  enumerating binary and ternary words, and checks signed crossing support
  through n=10. These are numerical checks, separately labelled from Lean.

The length-12 polynomial is

```
132 q^6 + 495 q^5 - 3135 q^4 + 5066 q^3 - 3384 q^2 + 827 q.
```

It agrees with existing repository data. Reproducing this polynomial is
cross-validation, not evidence of a new enumeration theorem.

## Validation and reproducibility

Pinned toolchain: Lean 4.19.0, existing pinned mathlib manifest unchanged.

```
lake build
lake env lean research/checkpoint_2026_10_18/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/partition_count.py --max-n 12 --word-check-n 8
python3 research/checkpoint_2026_10_18/join_controls.py
python3 research/checkpoint_2026_10_18/audit.py
```

The four new modules were built locally with the pinned kernel. The root
imports all four, and the GitHub workflow builds the whole project and
runs the new checks in addition to existing checks. Local source audit
and axiom output are retained in `logs/` and `data/`.

This host again needed the previously published `/proc/self/exe` lookup
shim to locate the Lean installation. It changes only that executable-path
lookup. The normal GitHub runner does not use it. The local full dependency
download was interrupted after narrowing the imports needed by the new
modules; the full project build is the independent GitHub gate.

## Sources and limits of the literature check

- Biedl et al., *The Complexity of Clickomania*, Theorem 2 and its proof:
  https://arxiv.org/pdf/cs/0107031 ; author bibliography:
  https://martindemaine.org/papers/ClickomaniaGameTheory2000/ .
  This supplies the known grammar and its ordinary mathematical connection
  to the game. That published theorem is not silently assumed by Lean.
- Sascha Kurz, *Polynomials for same game* (24 October 2001):
  https://oeis.org/A035617/a035617.pdf . Polynomiality and its degree bound
  predate this project; the listed coefficients are comparison data.
- Earlier source and novelty details remain in
  `../checkpoint_2026_10_17/SOURCE_AND_NOVELTY_REGISTER.md`.

Targeted searches for Same Game with noncrossing partitions and
inclusion-exclusion did not establish originality of this construction.
Search absence is not a novelty proof. The contribution claimed here is
the explicit formal counting layer, its limits, and independently checked
evidence useful for the next structural investigation.
