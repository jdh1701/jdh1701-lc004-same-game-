import LC004.NoncrossingInsertionIndex

namespace LC004

/-- Two finite collections of positions cross when some pair of positions
from the first alternates with a pair from the second. -/
def BlocksCross (xs ys : List Nat) : Prop :=
  ∃ u ∈ xs, ∃ v ∈ xs, ∃ s ∈ ys, ∃ t ∈ ys,
    PairCross u v s t

/-- No old pair, regardless of its endpoint order, can cross two
positions inside the newly inserted interval. -/
theorem shifted_old_pair_no_cross_new_interval
    (gap k u v s t : Nat) (hs : s < k) (ht : t < k) :
    ¬ PairCross (shiftAfterInsertion gap k u)
      (shiftAfterInsertion gap k v) (gap + s) (gap + t) := by
  unfold PairCross shiftAfterInsertion
  split_ifs <;> omega

/-- An arbitrary old block cannot cross any freshly inserted contiguous
block, with any size and any number of points. This includes triples. -/
theorem shifted_old_block_noncrossing_new_block
    (gap k : Nat) (old newOffsets : List Nat)
    (hnew : ∀ s ∈ newOffsets, s < k) :
    ¬ BlocksCross
       (old.map (shiftAfterInsertion gap k))
       (newOffsets.map (fun s => gap + s)) := by
  intro hcross
  rcases hcross with ⟨u, hu, v, hv, s, hs, t, ht, hcross⟩
  obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
  obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  exact (shifted_old_pair_no_cross_new_interval gap k u0 v0 s0 t0
    (hnew s0 hs0) (hnew t0 ht0)) hcross

/-- In particular, a triple inserted at consecutive indices cannot
cross ANY previously existing block of original positions. -/
theorem shifted_old_block_noncrossing_new_triple
    (gap : Nat) (old : List Nat) :
    ¬ BlocksCross
       (old.map (shiftAfterInsertion gap 3))
       [gap, gap+1, gap+2] := by
  have h := shifted_old_block_noncrossing_new_block
    gap 3 old [0,1,2] (by
      intro s hs
      simp only [List.mem_cons, List.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      all_goals omega)
  simpa only [List.map_cons, List.map_nil, Nat.add_zero] using h

end LC004
