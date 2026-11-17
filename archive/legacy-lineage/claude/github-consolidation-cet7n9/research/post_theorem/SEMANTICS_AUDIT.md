# Ordinary-word / Boolean RunState semantic audit

Source inspected: public `jdh1701/jdh1701-lc004-same-game-` at detached commit
`9204f839a68a8a7321fbcee1b9745784a1684788`.

## Definitions observed

- `LC004/RawEncoding.lean` defines `RawState := List Nat`, `encode`, and proves
  `encode_normalized`.
- `LC004/RunEncoding.lean` separately defines extensionally similar `Word`,
  `encodeRuns`, and proves `normalized_encodeRuns`.
- `LC004/ExecutableStep.lean` defines `stepAt` on Boolean run states.
- `LC004/IndexedMove.lean` defines relational `IndexedStep`.
- `LC004/ExecutableCorrespondence.lean` proves
  `stepAt s i = some t ↔ IndexedStep s i t`.
- There is no ordinary-word deletion relation or proven correspondence to it
  at this checkpoint.

## Independent exhaustive test

`check_correspondence.py` constructs maximal raw runs from cells, removes each
legal run by cell slicing, and independently implements the Boolean transition
by removing an indexed pair, merging equal boundary colors, and setting the
merged bit to true. For every word, it checks normalization, equality of legal
run indices, equality of encoded successors for every legal index, and equality
of complete successful deletion path counts (index sequences). Exact output is
in `results.jsonl`.

Exhaustive results:

| q | n through | ordinary words including empty | legal transitions checked | mismatch |
|---:|---:|---:|---:|---|
| 2 | 16 | 131,071 | 491,520 | none |
| 3 | 12 | 797,161 | 1,948,617 | none |
| 4 | 10 | 1,398,101 | 2,359,296 | none |

The critical singleton bridge is `0110`: delete run index 1 (`11`), yielding
raw `00` and encoded `(0,true)` from encoded `(0,false),(1,true),(0,false)`.

This is finite corroboration only, not a Lean proof or a substitute for
published ordinary-word semantics.

## Smallest counterexample to the proposed pointwise iff

The *particular* statement

```
ordinaryStep w i w' ↔ IndexedStep (encode w) i (encode w')
```

is false because `encode` forgets lengths above two. Take `w = 0011`, `i = 0`,
and `w' = 111`. Ordinary deletion produces `11`, not `111`. Yet both `11` and
`111` encode as `[(1,true)]`, so the right-hand side holds. The counterexample
does **not** refute successor correspondence or the Boolean quotient.

## Precise replacement statement

Define a deterministic `ordinaryStepAt : RawState → Nat → Option RawState`
that deletes a maximal run of length at least two at its *run index*. Then:

```
theorem encode_ordinaryStepAt (w : RawState) (i : Nat) :
  Option.map encode (ordinaryStepAt w i) = stepAt (encode w) i
```

Equivalently, if `OrdinaryIndexedStep w i w'` is the graph of that function:

```
IndexedStep (encode w) i t ↔
  ∃ w', OrdinaryIndexedStep w i w' ∧ encode w' = t
```

The forward direction follows from the functional commutation theorem and
`stepAt_iff_indexedStep`; the reverse is straightforward. From this, prove
the `follow` correspondence on lists of current run indices, then solvability,
successful first indices, and successful path equivalence. The fact that every
normalized Boolean state is represented by an ordinary word can separately
be shown with a decoder that expands false bits to one cell and true bits to
two cells.

Proof idea for the core commuting theorem: factor `w` into maximal runs with
positive lengths. Erasing a run leaves each other length unchanged except
when its two neighbors have equal color; then they form a new run of length
`l_left + l_right ≥ 2`. Thus capping at two commutes with the deletion in
both the merge and no-merge cases. This argument needs formalization.
