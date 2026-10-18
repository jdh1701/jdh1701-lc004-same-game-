# Factorization and the first permitted three-block threshold

Date: 2026-10-18. Base: `5e3f6856df0395f88b69e6c0fcd52cf0da9c4519`.
The objective remains general winning-word enumeration W(q,n). The problem
is not solved by this checkpoint.

## Formal progress and unchanged major-stage count

There are **9 major stages: 4 Lean-verified, 1 partial, 4 open**. Five still
need work. The count is unchanged because the new component results do not
complete another major stage. External novelty assessment is not a Lean task.

This checkpoint adds **11 named Lean theorems**, including helpers:

- Six in `CoefficientFactorization.lean`: uniqueness of lower-ideal sums,
  product factorization, signed coefficient collection/evaluation, and an
  unconditional coefficient theorem for Cartesian-product witness lists.
- Five in `NoncrossingRestriction.lean`: noncrossing restriction and blockwise
  reconstruction, block-cardinality preservation, and the pair/triple witness
  equivalence across the blocks of a noncrossing coarse partition.

The final targeted builds and all 11 axiom reports succeeded with Lean 4.19.0.
Only standard axioms `propext`, `Classical.choice`, and `Quot.sound` occur,
or subsets. Failed intermediate builds are retained and labelled separately.
`data/source_audit.json` lists exact theorem names, hashes, and the source scan.

[FACTORIZATION_ARGUMENT.md](FACTORIZATION_ARGUMENT.md) gives the mathematical
argument for the full component formula and identifies the remaining formal
assembly. In particular, the explicit product order isomorphism for partition
ideals and its coefficient transport are still needed. The executable witness
generator has not yet been identified with the formal witness predicate.
These gaps are not implicit axioms of the new theorems. Stage F also still
requires a useful general counting law and growth analysis.

## New engine and independence controls

`partition_counter.cpp` computes partition joins independently of the older
Python union-find implementation, using packed labels, a separate disjoint-set
implementation, and checked signed integer additions/negations. Both engines
share the Python witness generator and the same inclusion-exclusion algorithm;
their agreement is not wholly independent evidence of the witness model.

`test_engine.py` compared every coefficient, including its partition key, with
the Python engine at all lengths 0..10. It also reproduced all older full
polynomials through length 13. The new calculation evaluated 6,435 witnesses
at n=14 and obtained 33,113 nonzero signed terms.

At n=14 all 32,461 nontrivial component-factorization checks on nonzero support
passed. This does not test every zero coefficient at that length. The 651
nontrivial connected terms had size patterns (5,9), (6,8), and (7,7), in counts
154, 308, and 189. There was no block smaller than five. These are finite
computational observations; the minimum-five theorem remains unproved.

## Prospective length-14 result

Before computing n=14, the two structural hypotheses predicted

```text
R_14(q) = -3599q + 546q^2
W(q,14) = 429q^7 + 3003q^6 - 20020q^5 + 40495q^4
          - 38402q^3 + 18095q^2 - 3599q
W(3,14) = 657849
W(4,14) = 7012660
```

The full partition calculation matched the entire polynomial. The direct
raw-cell program independently confirmed both displayed colour counts.
The original prediction is preserved in `data/prediction14.json`, SHA-256
`a130caf443f5d102c3b94bad0c40175d4e0ca85374635d24c9fdcf601f9db133`.
This was a within-session prospective check, not an external preregistration.

## Discriminating length-15 test

The five-position condition first permits three connected blocks at n=15;
it does not require such terms. We therefore recorded a stronger rival model:
R_15 stays quadratic. Using the earlier polynomials and known one-/two-colour
counts, that model predicted

```text
R_15_quadratic(q) = -7555q - 3390q^2
W_quadratic(3,15) = 2003361
W_quadratic(4,15) = 25981780
```

The rival was recorded before either new n=15 calculation. Its SHA-256 is
`54da44b0d8441b8d54bc2b2e6312940bec709c12779d0c0179187a486ebcf51f`.

The direct raw-cell enumerator then found **2,003,151** winning three-colour
words among all 14,348,907 length-15 words. This falsifies the quadratic rival,
with a discrepancy of -210. Assuming the still-unproved degree bound of three,
the difference from the quadratic model must be `c q(q-1)(q-2)`. Its value at
q=3 forces c=-35, hence a conditional inference

```text
R_15(q) = -7625q - 3285q^2 - 35q^3
W(4,15) = 25980940
```

That inference was recorded **after** the raw q=3 result and **before** the
full n=15 join calculation finished. It must not be described as a blind
prediction of the q=3 count. Its record is `data/inference15_from_raw.json`.

The full partition calculation subsequently confirmed this inference exactly.
It processed **15,288 witnesses**, obtaining **93,272 nonzero signed terms**.
There are **35 connected three-block terms**, all with block sizes (5,5,5)
and coefficient -1. They produce the observed cubic coefficient -35. No
connected support term has a block smaller than five. All 35 partitions are
retained in `data/threshold15.json`. The computation took about 174 seconds.

The full resulting polynomial is

```text
W(q,15) = 5005q^7 - 17017q^6 + 7098q^5 + 38500q^4
          - 62455q^3 + 36495q^2 - 7625q.
```

The raw-cell and partition checks agree at all tested lengths and palettes.
There are 31 comparisons covering **379,437,301 labelled words** across the
tested lengths and palettes, with zero discrepancies.
The q=4 value at n=15 is a partition-computation result; it has not received
the independent raw-cell check performed for q=3 at that length.
The failure of the quadratic rival is a useful constraint: even if the
five-position theorem holds, genuinely new connected data becomes necessary
at n=15. This is finite evidence of a new interaction order, not a general
recurrence or a novelty claim.

## Reproduction

```sh
lake build
lake env lean research/checkpoint_2026_10_18/factorization/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/factorization/audit.py
c++ -std=c++17 -O3 -Wall -Wextra -pedantic research/checkpoint_2026_10_18/factorization/partition_counter.cpp -o /tmp/samegame-partition-counter
python3 research/checkpoint_2026_10_18/factorization/test_engine.py
python3 research/checkpoint_2026_10_18/factorization/threshold15.py test
c++ -std=c++17 -O3 -Wall -Wextra -pedantic research/checkpoint_2026_10_18/factorization/raw_counter15.cpp -o /tmp/samegame-raw-counter15
/tmp/samegame-raw-counter15 3 15 > research/checkpoint_2026_10_18/factorization/logs/raw_q3_n15.log
/tmp/samegame-raw-counter15 4 14 > research/checkpoint_2026_10_18/factorization/logs/raw_q4_n14.log
python3 research/checkpoint_2026_10_18/factorization/check_raw.py
```

The prediction and inference scripts deliberately refuse to overwrite their
historical records. CI repeats the full root Lean build, axiom audit, new join
checks through n=14, and raw q=3 through n=15/q=4 through n=14. The longer n=15
witness-join calculation is retained as local executed evidence, not rerun
by CI. The four-colour n=15 raw enumeration has not been performed.

The direct raw program is the previous counter with only its maximum length
and cell-buffer capacity increased. These executables are not Lean-verified
refinements. The final source audit is likewise not a substitute for the
compiler or CI build.

## Next mathematical and formal targets

1. Assemble the partition-ideal product isomorphism and coefficient transport
   into a single Lean component-factorization theorem.
2. Prove cancellation for connected terms containing four-position blocks,
   or find a counterexample to the minimum-five hypothesis at a later length.
3. Determine the new connected coefficients without relying on already known
   W(q,n) values. Otherwise the cumulant transform only repackages the problem.
4. Complete the raw-game/grammar converse, generator correctness, executable
   refinement, and end-to-end theorem from the existing roadmap.

The new algebraic machinery is standard, and no novelty assessment has been
completed for the Same Game specialization or the new finite coefficients.
