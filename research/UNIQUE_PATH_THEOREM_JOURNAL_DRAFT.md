# A Kernel-Checked Uniqueness Theorem for the One-Dimensional Same Game

## Critical-Pair Exchange, Monotone Simulation, and Formal Verification in Lean 4

**Research draft — 22 September 2026**

### Abstract

We prove, for a normalized nonempty run-state model of the one-dimensional Same Game, that uniqueness of the successful first deletion is equivalent to uniqueness of the complete successful deletion path. The result is formalized in Lean 4 and compiled in a clean repository without `sorry`, `admit`, `sorryAx`, or project-defined axioms. It is not a solution of the longstanding enumeration problem for winning q-ary strings with q >= 3; rather, it is a structural theorem discovered while attacking that problem. The proof combines a run-length quotient, a color-preserving heaviness relation, full deletion simulation, explicit no-merge and bridge critical-pair analysis, boundary-aware context transport, and a final exchange induction.

## Main theorem

For every normalized nonempty run state `s`:

```lean
theorem unconditional_executable_unique_first_iff_path
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulFirst s ↔ UniqueSuccessfulPath s := by
  exact final_executable_unique_first_iff_path
    noMergeStructuralExchange_proved
    normalizedBridgeStructuralExchange_proved
    hn hne
```

The relational capstone is:

```lean
theorem unconditional_unique_choice_iff_unique_path
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulChoice s ↔ UniqueCompletePath s := by
  exact final_unique_choice_iff_unique_path
    noMergeStructuralExchange_proved
    normalizedBridgeStructuralExchange_proved
    hn hne
```

## Formal model

```lean
abbrev RunState := List (Nat × Bool)
```

Colors are natural numbers and the Boolean component records heaviness/deletability. A legal deletion removes a heavy run and merges newly exposed equal-colored neighbors into a heavy run.

The executable predicates are `SuccessfulMove`, `SuccessfulPath`, `UniqueSuccessfulFirst`, and `UniqueSuccessfulPath`. Normalization requires adjacent runs to have different colors.

## Proof architecture

The proof establishes a color-skeleton-preserving `Heavier` relation and full deletion simulation, yielding monotonicity of solvability. It then introduces `ExchangeDominates`: an alternate successor dominates a child result if it is already heavier, or if one indexed move reaches a heavier state.

No-merge exchange is decomposed into left endpoint, right endpoint, far-left, adjacent-left, adjacent-right, and far-right cases. Bridge exchange is decomposed analogously. The exact-boundary cases require explicit critical-pair analysis because deletion can expose equal colors across a context boundary.

### Formalization-discovered null results

1. Generic exact-boundary prefix transport is false.
2. The adjacent-left proof must explicitly handle the possibility that the two runs separated by the selected run have the same color.
3. Far-right prefix stripping requires a boundary-aware zero-index lift.
4. Witness interfaces used for safe prefix transport must retain nonzero compensating indices.

A representative counterexample to naïve boundary transport is:

`ctx=[(0,false)]`, `s=[(1,true),(0,false)]`.

Locally deleting index zero leaves `[(0,false)]`; globally the corresponding deletion in `[(0,false),(1,true),(0,false)]` merges the exposed color-0 runs and produces `[(0,true)]`.

## Verification

- Planned mathematical obligations: **18/18 green**
- Unconditional relational theorem: **green**
- Unconditional executable theorem: **green**
- Full root build: **green**
- `sorry`: **0** on cleaned default branch
- `admit`: **0**
- `sorryAx`: **0**
- project-defined `axiom`: **0**
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`
- clean repository checkpoint: **9204f839…**

## Computational discovery lineage

Before formal closure, exact exhaustive searches reported zero counterexamples to the uniqueness conjecture in several finite universes, including q=3 through n<=12, q=2 through n<=14, and q=4 through n<=9. These computations motivated the conjecture but were never treated as proof.

## Relation to the open enumeration problem

The theorem does **not** itself solve the q>=3 winning-string enumeration problem. Its prospective value is structural: it isolates an unambiguous subclass of successful reductions. A plausible route toward enumeration is to classify the complementary branching states, obtain a canonical non-overcounting decomposition, and derive functional or generating equations.

## Novelty status

Targeted project searches did not locate this exact uniqueness theorem or its associated unique-path counting data in the Same Game literature. The defensible present description is **apparently novel and Lean-verified**, while absolute bibliographic priority remains to be established.

## References

- T. C. Biedl, E. D. Demaine, M. L. Demaine, R. Fleischer, L. Jacobsen, J. I. Munro, *The Complexity of Clickomania*, More Games of No Chance, MSRI Publications 42 (2002).
- C. Burns and B. Purcell, *Counting the number of winning binary strings in the 1-dimensional same game*, Fibonacci Quarterly 45(3) (2007), 233–238.
- OEIS A035615, A035617, A065237–A065243.
