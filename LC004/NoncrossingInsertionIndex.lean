import LC004.FourBlockCrossing

namespace LC004

/-- The index of an old position after inserting k new cells at gap. -/
def shiftAfterInsertion (gap k i : Nat) : Nat :=
  if i < gap then i else i + k

/-- The old positions retain their order after inserting a block. -/
theorem shiftAfterInsertion_strict
    (gap k i j : Nat) (hij : i < j) :
    shiftAfterInsertion gap k i < shiftAfterInsertion gap k j := by
  unfold shiftAfterInsertion
  split_ifs <;> omega

/-- No old position maps inside the open inserted interval. -/
theorem shifted_old_outside_new_block
    (gap k i s : Nat) (hs : s < k) :
    shiftAfterInsertion gap k i ≠ gap + s := by
  unfold shiftAfterInsertion
  split_ifs <;> omega

/-- The crossing relation between two old pairs is invariant under
the order-preserving index shift. -/
theorem pairCross_shift_iff
    (gap k u v x y : Nat) :
    PairCross (shiftAfterInsertion gap k u)
      (shiftAfterInsertion gap k v)
      (shiftAfterInsertion gap k x)
      (shiftAfterInsertion gap k y)
    ↔ PairCross u v x y := by
  unfold PairCross shiftAfterInsertion
  split_ifs <;> omega

/-- An old ordered pair cannot cross any pair lying entirely inside
the freshly inserted consecutive block. Old endpoints may surround
the whole inserted block, which is nesting rather than crossing. -/
theorem old_pair_not_cross_new_pair
    (gap k u v s t : Nat)
    (huv : u < v) (hst : s < t) (htk : t < k) :
    ¬ PairCross (shiftAfterInsertion gap k u)
         (shiftAfterInsertion gap k v) (gap+s) (gap+t) := by
  unfold PairCross shiftAfterInsertion
  split_ifs <;> omega

end LC004
