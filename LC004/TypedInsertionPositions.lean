import LC004.NoncrossingBlockFamily

namespace LC004

/-- The old positions, now bounded by the length after insertion. -/
def oldPosition {n : Nat} (gap k : Nat) (i : Fin n) : Fin (n + k) :=
  ⟨shiftAfterInsertion gap k i.val, by
    have hi := i.isLt
    unfold shiftAfterInsertion
    split_ifs <;> omega⟩

/-- The fresh positions. A valid gap can include the final gap n. -/
def freshPosition {n : Nat} (gap k : Nat) (hgap : gap ≤ n)
    (s : Fin k) : Fin (n + k) :=
  ⟨gap + s.val, by have hs := s.isLt; omega⟩

theorem oldPosition_injective {n : Nat} (gap k : Nat) :
    Function.Injective (oldPosition (n := n) gap k) := by
  intro i j h
  have heq := congrArg Fin.val h
  change shiftAfterInsertion gap k i.val =
    shiftAfterInsertion gap k j.val at heq
  apply Fin.ext
  unfold shiftAfterInsertion at heq
  split_ifs at heq <;> omega

theorem freshPosition_injective {n : Nat} (gap k : Nat)
    (hgap : gap ≤ n) :
    Function.Injective (freshPosition gap k hgap) := by
  intro i j h
  have heq := congrArg Fin.val h
  change gap + i.val = gap + j.val at heq
  apply Fin.ext
  omega

theorem oldPosition_ne_freshPosition {n : Nat} (gap k : Nat)
    (hgap : gap ≤ n) (i : Fin n) (s : Fin k) :
    oldPosition gap k i ≠ freshPosition gap k hgap s := by
  intro h
  exact shifted_old_outside_new_block gap k i.val s.val s.isLt
    (congrArg Fin.val h)

/-- Every bounded output position is old or fresh. Combined with
injectivity and disjointness, this says insertion covers exactly once. -/
theorem insertion_positions_cover {n : Nat} (gap k : Nat)
    (hgap : gap ≤ n) (j : Fin (n + k)) :
    (∃ i : Fin n, oldPosition gap k i = j) ∨
    (∃ s : Fin k, freshPosition gap k hgap s = j) := by
  have hj := j.isLt
  by_cases hleft : j.val < gap
  · left
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    apply Fin.ext
    change shiftAfterInsertion gap k j.val = j.val
    simp [shiftAfterInsertion, hleft]
  · by_cases hinside : j.val < gap + k
    · right
      refine ⟨⟨j.val - gap, by omega⟩, ?_⟩
      apply Fin.ext
      change gap + (j.val - gap) = j.val
      omega
    · left
      refine ⟨⟨j.val - k, by omega⟩, ?_⟩
      apply Fin.ext
      change shiftAfterInsertion gap k (j.val - k) = j.val
      have hafter : ¬ j.val - k < gap := by omega
      simp only [shiftAfterInsertion, if_neg hafter]
      omega

/-- A complete certificate states all required invariants explicitly.
The flattened partition is a permutation of all bounded positions,
so duplicate occurrences, omitted cells, and overlapping blocks are
excluded. Noncrossing uses the existing size-at-most-three predicate. -/
structure Noncrossing23Certificate {n q : Nat}
    (color : Fin n → Fin q) where
  blocks : List (List (Fin n))
  sizes : ∀ b ∈ blocks, b.length = 2 ∨ b.length = 3
  exactCover : blocks.flatten.Perm (List.finRange n)
  monochromatic : ∀ b ∈ blocks, ∃ a : Fin q, ∀ p ∈ b, color p = a
  noncrossing : NoncrossingBlockFamily (blocks.map (List.map Fin.val))

/-- Regression witness for the rejected unrestricted insertion claim. -/
theorem four_position_block_crosses_itself (gap : Nat) :
    BlocksCross [gap, gap+1, gap+2, gap+3]
      [gap, gap+1, gap+2, gap+3] := by
  refine ⟨gap, by simp, gap+2, by simp,
    gap+1, by simp, gap+3, by simp, ?_⟩
  unfold PairCross
  omega

#print axioms oldPosition_injective
#print axioms freshPosition_injective
#print axioms oldPosition_ne_freshPosition
#print axioms insertion_positions_cover
#print axioms four_position_block_crosses_itself
#print axioms noncrossing_block_family_insert

end LC004
