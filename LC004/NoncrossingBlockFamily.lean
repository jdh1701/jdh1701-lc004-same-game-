import LC004.BlockCrossingInsertion

namespace LC004

/-- All blocks in a family are pairwise noncrossing. -/
def NoncrossingBlockFamily (blocks : List (List Nat)) : Prop :=
  ∀ a ∈ blocks, ∀ b ∈ blocks, ¬ BlocksCross a b

/-- Shift every index of every old block through an insertion gap. -/
def shiftBlock (gap k : Nat) (block : List Nat) : List Nat :=
  block.map (shiftAfterInsertion gap k)

theorem pairCross_symmetric (u v s t : Nat) :
    PairCross u v s t ↔ PairCross s t u v := by
  unfold PairCross
  tauto

theorem blocksCross_symmetric (a b : List Nat) :
    BlocksCross a b ↔ BlocksCross b a := by
  constructor
  · rintro ⟨u,hu,v,hv,s,hs,t,ht,hc⟩
    exact ⟨s,hs,t,ht,u,hu,v,hv,(pairCross_symmetric u v s t).mp hc⟩
  · rintro ⟨s,hs,t,ht,u,hu,v,hv,hc⟩
    exact ⟨u,hu,v,hv,s,hs,t,ht,(pairCross_symmetric u v s t).mpr hc⟩

/-- Index shifting preserves the crossing relation between arbitrary
old blocks, not merely between pairs. -/
theorem blocksCross_shift_iff (gap k : Nat) (a b : List Nat) :
    BlocksCross (shiftBlock gap k a) (shiftBlock gap k b)
      ↔ BlocksCross a b := by
  constructor
  · rintro ⟨u,hu,v,hv,s,hs,t,ht,hc⟩
    obtain ⟨u0,hu0,rfl⟩ := List.mem_map.mp hu
    obtain ⟨v0,hv0,rfl⟩ := List.mem_map.mp hv
    obtain ⟨s0,hs0,rfl⟩ := List.mem_map.mp hs
    obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
    exact ⟨u0,hu0,v0,hv0,s0,hs0,t0,ht0,
      (pairCross_shift_iff gap k u0 v0 s0 t0).mp hc⟩
  · rintro ⟨u,hu,v,hv,s,hs,t,ht,hc⟩
    exact ⟨shiftAfterInsertion gap k u, List.mem_map.mpr ⟨u,hu,rfl⟩,
      shiftAfterInsertion gap k v, List.mem_map.mpr ⟨v,hv,rfl⟩,
      shiftAfterInsertion gap k s, List.mem_map.mpr ⟨s,hs,rfl⟩,
      shiftAfterInsertion gap k t, List.mem_map.mpr ⟨t,ht,rfl⟩,
      (pairCross_shift_iff gap k u v s t).mpr hc⟩

theorem noncrossing_block_family_shift
    (blocks : List (List Nat)) (gap k : Nat)
    (h : NoncrossingBlockFamily blocks) :
    NoncrossingBlockFamily (blocks.map (shiftBlock gap k)) := by
  intro a ha b hb
  obtain ⟨a0,ha0,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b0,hb0,rfl⟩ := List.mem_map.mp hb
  exact (blocksCross_shift_iff gap k a0 b0).not.mpr (h a0 ha0 b0 hb0)

/-- A contiguous new block is noncrossing with every shifted old block,
so inserting it preserves pairwise noncrossing for a whole family.
The result allows ANY k, including both pair and triple insertions. -/
theorem noncrossing_block_family_insert
    (blocks : List (List Nat)) (gap k : Nat)
    (hk : k ≤ 3)
    (h : NoncrossingBlockFamily blocks) :
    NoncrossingBlockFamily
      ((List.range k).map (fun s => gap + s) ::
        blocks.map (shiftBlock gap k)) := by
  let fresh := (List.range k).map (fun s => gap + s)
  have hnew : ∀ s ∈ List.range k, s < k := by
    intro s hs
    simpa using hs
  have hdisjoint (old : List Nat) :
      ¬ BlocksCross (shiftBlock gap k old) fresh :=
    shifted_old_block_noncrossing_new_block gap k old (List.range k) hnew
  have hself : ¬ BlocksCross fresh fresh := by
    intro hc
    rcases hc with ⟨u,hu,v,hv,s,hs,t,ht,hcross⟩
    obtain ⟨u0,hu0,rfl⟩ := List.mem_map.mp hu
    obtain ⟨v0,hv0,rfl⟩ := List.mem_map.mp hv
    obtain ⟨s0,hs0,rfl⟩ := List.mem_map.mp hs
    obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
    have huBound := hnew u0 hu0
    have hvBound := hnew v0 hv0
    have hsBound := hnew s0 hs0
    have htBound := hnew t0 ht0
    unfold PairCross at hcross
    omega
  intro a ha b hb
  simp only [List.mem_cons] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · subst b
      exact hself
    · obtain ⟨old,hold,heq⟩ := List.mem_map.mp hb
      rw [← heq]
      exact (blocksCross_symmetric fresh (shiftBlock gap k old)).not.mpr
        (hdisjoint old)
  · obtain ⟨old,hold,heq⟩ := List.mem_map.mp ha
    rw [← heq]
    rcases hb with hb | hb
    · subst b
      exact hdisjoint old
    · obtain ⟨old2,hold2,heq2⟩ := List.mem_map.mp hb
      rw [← heq2]
      exact (blocksCross_shift_iff gap k old old2).not.mpr
        (h old hold old2 hold2)

end LC004
