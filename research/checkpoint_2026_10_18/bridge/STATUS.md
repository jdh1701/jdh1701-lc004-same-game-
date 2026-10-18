# Raw grammar bridge and connected counting hypotheses

Date: 2026-10-18. Base commit: `c04443b029ff85da4fad7ecc65f2d6e29f9aabb2`.

The target remains a general enumeration of winning words W(q,n), with each
word counted once under legal maximal-run deletions. This checkpoint advances
a semantic proof and tests structural hypotheses aimed at that unresolved
problem. It does not claim a solution or a new general recurrence theorem.

## Fixed stage count

| Stage | Obligation | Status |
|---|---|---|
| A | Raw/run moves and successful paths correspond | Lean verified |
| B | Raw solvability iff grammar membership | Partial: raw-solvable implies grammar verified; converse open |
| C1 | Grammar iff first-block decomposition | Lean verified |
| C2 | Finite partition generator is sound and complete | Open |
| D | Event intersections are joins; event cardinality is q^blocks | Lean verified |
| E1 | Signed union counts each covered word once | Lean verified |
| E2 | Executable compressed coefficient map refines the specification | Open |
| F | Useful general structural law or recurrence, with growth analysis | Open |
| G | End-to-end W(q,n) theorem and external novelty assessment | Open |

**9 stages: 4 verified, 1 partial, 4 open.** Five stages still need work.
Stages have unequal difficulty, and external novelty assessment is not a task
Lean can certify. This is not a percentage-complete estimate.
`STAGES.json` records the stage evidence. There are **12 additional named Lean
theorems**, including helpers, in this checkpoint. They do not count as 12
completed stages.

## What Lean now checks

`GrammarInsertion.lean` proves that a grammar word can be inserted at any cell
boundary of another grammar word, and that every constant word of length at
least two is in the grammar. `OrdinaryGrammarComplete.lean` derives a deletion
decomposition from the actual implementation `ordinaryStepAtFuel`, then proves:

```lean
theorem ordinarySolvable_clickGrammar {w : RawState}
    (h : OrdinarySolvable ordinaryStepAt w) : ClickGrammar w
```

It also transfers this conclusion to `FirstBlock`. The proof is universal in
the word and the successful move sequence. It does not assume the grammar
characterization of the game. The converse, grammar implies a legal maximal-run
solution, remains unproved here.

The existing raw game definitions were extracted into `LC004/RawGame.lean`
without changing their bodies or names. Four definition hashes are checked
against the previous commit by `audit_progress.py`; `RawState` remains `List Nat`.
The root imports the new modules. This refactor lets the grammar proof compile
without importing the whole older run-based proof stack.

All 12 new theorem names and source hashes appear in `data/progress_audit.json`.
`logs/bridge_attempt2.log` records a successful pinned Lean 4.19.0 build.
`logs/axioms_verified.log` contains the actual signature and axiom output:
all 12 use only subsets of `propext` and `Quot.sound`. The source audit found
no proof holes, project-specific axioms, unsafe overrides, or `native_decide`.
The full repository build is an additional GitHub Actions gate; local targeted
build success alone does not assert that gate has passed.

## Structural investigation aimed at enumeration

Let a(p) be the signed coefficient at equality partition p from the full
pair/triple witness union. Let NC(p) be its noncrossing closure, formed by
merging crossing blocks until no crossings remain. The following are distinct
hypotheses, not Lean theorems.

**H1: component factorization.** For the blocks B of NC(p),

`a(p) = product_B a(standardize(p restricted to B))`.

`connected_weights.py` tested all equality partitions through n=10 and all
nonzero signed support at n=11,12. It passed **15,325 nontrivial factorization
checks** using at least two strictly smaller components. Single-component
identities were not counted as evidence. The run also checked **128,825 zero
coefficients**, including partitions with singleton blocks. These are finite
checks; support-only checks at 11 and 12 do not test every missing coefficient.

Define R_n(q) to sum a(p) q^(number of blocks of p) over partitions whose
noncrossing closure is one block. If H1 holds in general, these connected
polynomials give the formal series identity

`M_q(z) = 1 + sum_(k>=1) R_k(q) (z M_q(z))^k`,

where `M_q(z) = sum_(n>=0) W(q,n) z^n`, subject also to the witness/game
correspondence. The formal transform of the independently enumerated old
raw/run polynomials agrees with the connected sums through n=12. The displayed
identity defines a triangular transform for any M; by itself it is not a new
way to compute the unknown connected polynomials.

Two simpler models were falsified:

- Factorization over the original individual blocks fails at p=0101: actual
  coefficient 0, proposed product 1.
- The linear rule `R_n(q)=q R_n(1)` fits through n=9 but fails at n=10:
  `R_10(q)=-161q-5q^2`, whereas the rule predicts `-166q`.

**H2: minimum block size in nontrivial connected support.** If a(p) is nonzero,
NC(p) has one block, and p has at least two blocks, then every block of p has
at least five positions. No counterexample occurred through n=13. At n=10,11,12,
the nontrivial connected support has respectively 5,22,78 terms; at n=13 it has
234 terms, with size patterns (5,8) in 91 cases and (6,7) in 143 cases.

If H1 and H2 hold, `degree R_n <= max(1, floor(n/5))` for n>=1. This is a
potential reduction in the new connected data needed at each length. It does
not determine all that data at larger lengths and is not a solution by itself.

## Prospective length-13 test

Before computing the n=13 witness union, `predict_length13.py` used only the
existing n<=12 polynomials, W(1,13)=1, and W(2,13)=5878. The latter agrees with
the existing binary raw census and the known binary formula. Under H1 and H2,
R_13 has degree at most two, so those inputs predict:

```text
R_13(q) = 807q + 403q^2
W(q,13) = 1287q^6 - 4290q^5 + 4004q^4 + 585q^3 - 2392q^2 + 807q
W(3,13) = 216765
W(4,13) = 1906012
```

The prediction was recorded and communicated before the new calculation.
`data/prediction_length13.json` has SHA-256
`77160a5c2a339630c53a4ef3a4aae460a420406c1eda7afd6055c2db23bacd6b`.
Its historical status text is deliberately retained. This is a within-session
prospective check, not an external preregistration.

`holdout_length13.py` then processed all 2,717 witnesses and found 11,883
nonzero signed terms. **The entire predicted polynomial matched**, and H2 had
no counterexample. Runtime was about 116 seconds. Full connected terms and
the prediction hash are saved in `data/holdout_length13.json`.

A separate C++ program, `raw_counter.cpp`, enumerates labelled cell words and
deletes entire maximal runs directly. It does not use grammar witnesses,
partition coefficients, or orbit canonicalization. It confirmed the predicted
three- and four-colour values at n=13, and agreed with the older polynomials
at every length 0..12. Across the 28 comparisons, **91,869,969 labelled words**
were examined, with zero discrepancies. See `data/raw_crosscheck.json` and
the literal `logs/raw_q*_n13.log` outputs. These are computational results,
not kernel-checked counting certificates.

## Next work

1. Complete stage B by proving grammar membership implies solvability under
   maximal-run deletion. A possible route is relaxed monochromatic-block
   erasure followed by a normalization argument using run monotonicity; that
   route is not yet established.
2. Prove H1 from witness restrictions and the signed union identity. This
   would establish a meaningful general decomposition, not merely a fit.
3. Attack H2 structurally: blocks of size two or three are forced whole in
   every refining witness; size four introduces two possible pairings and
   requires a genuine cancellation argument. These are proof ideas, not claims.
4. Continue C2 and E2 to connect an executable partition calculation to the
   formal game. A useful recurrence and its growth analysis remain necessary
   for F; the end-to-end conclusion and literature assessment remain G.

## Reproduction and provenance

```sh
lake build
lake env lean research/checkpoint_2026_10_18/bridge/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/bridge/audit_progress.py
python3 research/checkpoint_2026_10_18/bridge/connected_weights.py
python3 research/checkpoint_2026_10_18/bridge/inspect_connected_patterns.py
python3 research/checkpoint_2026_10_18/bridge/holdout_length13.py
c++ -std=c++17 -O2 -Wall -Wextra -pedantic research/checkpoint_2026_10_18/bridge/raw_counter.cpp -o /tmp/samegame-raw-counter
/tmp/samegame-raw-counter 3 13 > research/checkpoint_2026_10_18/bridge/logs/raw_q3_n13.log
/tmp/samegame-raw-counter 4 13 > research/checkpoint_2026_10_18/bridge/logs/raw_q4_n13.log
python3 research/checkpoint_2026_10_18/bridge/check_raw_counts.py
```

`predict_length13.py` deliberately refuses to overwrite the original prediction.
The GitHub workflow repeats the full Lean build, axiom report, n<=12 structural
checks, and independent raw counts. It does not repeat the slower n=13 witness
join computation. That computation's executed output is retained separately.
Local Lean uses the previously documented executable-path lookup shim; no
kernel or proof logic is changed. GitHub uses the normal pinned toolchain.

Primary background: Franz Lehner, *Free cumulants and enumeration of connected
partitions*, https://arxiv.org/pdf/math/0110030 . Its noncrossing-closure and
formal cumulant framework motivates the decomposition, but does not prove H1
for the Same Game signed weights. Targeted literature searches did not settle
whether H1, H2, or their application here is new. The older grammar and binary
enumeration sources are recorded in the parent checkpoint and source register.
No originality or solved-problem claim is made.
