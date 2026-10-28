import LC004.NoncrossingInsertionIndex

namespace LC004

/-- An unordered collection of indexed pairs is pairwise noncrossing
if no pair's endpoints alternate with another pair's endpoints. -/
def PairFamilyNoncrossing (edges : List (Nat × Nat)) : Prop :=
  ∀ e ∈ edges, ∀ f ∈ edges,
    ¬ PairCross e.1 e.2 f.1 f.2

/-- Old pairs move under an insertion by shifting each endpoint. -/
def shiftPair (gap k : Nat) (e : Nat × Nat) : Nat × Nat :=
  (shiftAfterInsertion gap k e.1, shiftAfterInsertion gap k e.2)

/-- All existing pair crossings are preserved when a new contiguous
block is inserted, independently of the size of that block. -/
theorem pairFamily_noncrossing_shift
    (edges : List (Nat × Nat)) (gap k : Nat)
    (h : PairFamilyNoncrossing edges) :
    PairFamilyNoncrossing (edges.map (shiftPair gap k)) := by
  intro e he f hf
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
  change ¬ PairCross (shiftAfterInsertion gap k e0.1)
    (shiftAfterInsertion gap k e0.2)
    (shiftAfterInsertion gap k f0.1)
    (shiftAfterInsertion gap k f0.2)
  exact (pairCross_shift_iff gap k e0.1 e0.2 f0.1 f0.2).not.mpr
    (h e0 he0 f0 hf0)

/-- Inserting a disjoint adjacent new pair produces no crossings
with any previously noncrossing family of ordered old pairs. -/
theorem pairFamily_noncrossing_insert_pair
    (edges : List (Nat × Nat)) (gap k : Nat) (hk : 2 ≤ k)
    (hordered : ∀ e ∈ edges, e.1 < e.2)
    (h : PairFamilyNoncrossing edges) :
    PairFamilyNoncrossing
      ((gap, gap + 1) :: edges.map (shiftPair gap k)) := by
  intro e he f hf
  simp only [List.mem_cons] at he hf
  rcases he with heNew | heOld
  · rw [heNew]
    rcases hf with hfNew | hfOld
    · rw [hfNew]
      unfold PairCross
      omega
    · obtain ⟨f0, hf0, hfEq⟩ := List.mem_map.mp hfOld
      rw [← hfEq]
      change ¬ PairCross gap (gap + 1)
          (shiftAfterInsertion gap k f0.1)
          (shiftAfterInsertion gap k f0.2)
      have hno := old_pair_not_cross_new_pair gap k f0.1 f0.2 0 1
        (hordered f0 hf0) (by omega) (by omega)
      unfold PairCross at hno ⊢
      omega
  · obtain ⟨e0, he0, heEq⟩ := List.mem_map.mp heOld
    rw [← heEq]
    rcases hf with hfNew | hfOld
    · rw [hfNew]
      change ¬ PairCross (shiftAfterInsertion gap k e0.1)
          (shiftAfterInsertion gap k e0.2) gap (gap + 1)
      exact old_pair_not_cross_new_pair gap k e0.1 e0.2 0 1
        (hordered e0 he0) (by omega) (by omega)
    · obtain ⟨f0, hf0, hfEq⟩ := List.mem_map.mp hfOld
      rw [← hfEq]
      change ¬ PairCross (shiftAfterInsertion gap k e0.1)
          (shiftAfterInsertion gap k e0.2)
          (shiftAfterInsertion gap k f0.1)
          (shiftAfterInsertion gap k f0.2)
      exact (pairCross_shift_iff gap k e0.1 e0.2 f0.1 f0.2).not.mpr
        (h e0 he0 f0 hf0)

end LC004
