# LC004 consolidation — what we have, and what to solve next

Consolidated 2026-10-01 from `main` (`a9cb335`) and both open draft PRs.

## 1. Inventory and verdict

| Source | What it is | Verdict |
|---|---|---|
| `main` — `LC004/` (68 modules, ~4.6k lines Lean) | Unconditional theorem: for normalized nonempty `RunState`, unique successful first move ⇔ unique successful path. No `sorry`/axioms beyond `propext`, `Classical.choice`, `Quot.sound`. | **Core result. Keep.** |
| `main` — `scripts/`, `research/exhaustive_structure.py`, `verification/` | Exhaustive finite checks that motivated the theorem. | Keep. Re-run 2026-10-01: all failure counts 0. |
| PR #1 `research/post-theorem-wub-census-2026-09-23` | W/U/B census, ordinary-word semantics audit, Biedl grammar audit, pair-commutation data, conditional Lean transfer module. | **Merged into this branch** under `research/post_theorem/`. Root Lean imports unchanged. |
| PR #2 `research/consolidated-333-lean` | "AlexandriaComplexity": Tseitin/resolution-width certificates, XOR span, Turing-machine tape lemmas, P-vs-NP framing. Lean 4.34.0 (main is pinned to 4.19.0). | **Not merged.** Unrelated to Same Game; belongs in its own repo. Nothing in it is used by LC004. |

## 2. What is actually established

**Proved in Lean (main):**
- `unconditional_executable_unique_first_iff_path` and the relational
  `unconditional_unique_choice_iff_unique_path` (`LC004/UnconditionalFinal.lean`).
- `stepAt s i = some t ↔ IndexedStep s i t` (`ExecutableCorrespondence.lean`).
- `encode_normalized` for raw words (`RawEncoding.lean`).

**Proved in Lean, but only on a research path (PR #1, not in root):**
- `research/post_theorem/OrdinaryCorrespondence.lean`: defines `ordinaryStepAt`
  on raw cell words and proves that path, solvability, unique-first and
  unique-path all transfer from `RunState` to ordinary words, **conditional on**
  `hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i`.

**Finite evidence only:**
- `hcommute` holds for `ordinaryStepAt` on every word with q=2 n≤16, q=3 n≤12,
  q=4 n≤10 (re-run 2026-10-01, 0 mismatches over 4.8M edges).
- Ordinary W counts match OEIS A035615 / A035617 and Kurz's polynomial.
- U/W falls with n (q=3: 15.4% at n=10 → 6.2% at n=13). The branching
  complement B dominates and its canonical-state count keeps growing.
- 88% (q=3,n=13) of successful first-move pairs commute exactly in two steps;
  the rest are adjacent bridge critical pairs.

**Refuted (useful negatives):**
- Pointwise `OrdinaryStep w i w' ↔ IndexedStep (encode w) i (encode w')` is false
  (`w=0011, i=0, w'=111`). The functional commuting square is the right target.
- Biedl et al.'s grammar does not track path ambiguity: `aaaa` has P=1, G=2;
  `aabb` has P=2, G=1. Parse counts can't be used to count unique paths.
- Generic exact-boundary prefix transport is false (see journal draft).

**Not established anywhere:** a q≥3 enumeration formula, any generating
function, literature priority.

## 3. The gap

The headline theorem is about the abstract `RunState` model. It says nothing
yet about actual Same Game words like `0110`. The bridge exists except for a
single lemma, `hcommute`, which has 4.8M finite confirmations and no proof.

## 4. Next problem: prove `hcommute` — done (2026-10-29)

**Status:** proved in `LC004/OrdinaryCommute.lean` and imported from the root.
`OrdinaryCorrespondence.lean` was promoted from `research/post_theorem/` into
`LC004/`. The ordinary-word capstone is

```lean
theorem ordinary_unique_first_iff_unique_path
    (w : RawState) (hne : w ≠ []) :
    OrdinaryUniqueFirst w ↔ OrdinaryUniquePath w
```

i.e. the uniqueness theorem now holds for actual Same Game words, with run
indices counted in the raw word. The commuting lemma itself was compiled
standalone against core Lean 4.19.0 (axioms: `propext`, `Quot.sound`); the
full Mathlib build is checked by CI. The original plan is kept below.

### Original plan

```lean
theorem ordinaryStepAt_commute (w : RawState) (i : Nat) :
    Option.map encode (ordinaryStepAt w i) = stepAt (encode w) i
```

Why this one:
- **Small and well-specified.** Pure list reasoning about run-length encoding;
  no game-tree induction.
- **High payoff.** Once proved, instantiate `ordinaryUniqueFirst_iff` and
  `ordinaryUniquePath_iff` to get the theorem for real Same Game words, then
  move `OrdinaryCorrespondence.lean` into `LC004/` and the root import list.
- **Low risk.** Exhaustive checks say it's true; the only trap (the `0011` case)
  is already understood.

Suggested proof plan:
1. Replace the fuel-based `ordinaryStepAtFuel` with structural recursion on
   `encode`-aligned run decomposition (or prove fuel ≥ length suffices).
2. Lemma: `encode (c :: same ++ rest)` where `rest` doesn't start with `c` is
   `(c, same ≠ []) :: encode rest`.
3. Lemma: `encode (xs ++ ys)` merges the last run of `xs` with the first run
   of `ys` when colors match, setting the bit to `true` (this is the bridge case
   and must match `stepAt`'s merge exactly).
4. Induct on `i` along the run decomposition; case `i = 0` vs `i+1`, with a
   boundary case analysis for the bridge merge.

Prerequisites: install elan / Lean 4.19.0 (not present in this container), and
add `ordinaryStepAt_commute` to a non-root module first, then promote.

## 5. After that (research, not yet tractable)

- **Trace-quotient enumeration.** Pair data suggests counting paths modulo
  commuting independent moves, with adjacent bridge pairs as the only
  non-commuting relations. Test whether this compresses B before investing
  in a recurrence. If it doesn't, the census suggests a major new idea is
  needed for q≥3 enumeration (PR #1's provisional "decision B").
- **Literature priority.** Full audit of Burns–Purcell and later work before
  any novelty claim.

## 6. Housekeeping

- Close PR #1 as superseded by this branch, or merge this branch instead.
- Move PR #2 to its own repository; its Lean toolchain (4.34.0) and subject
  matter are independent of LC004.
- `.github/workflows/lean.yml` only runs on `main`, so research branches get
  no CI. Consider adding `pull_request` triggers.
