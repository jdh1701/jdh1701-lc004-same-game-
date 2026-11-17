import LC004.FourGapWitnesses

namespace LC004

/-- The three open interior gaps and the cyclic exterior gap. -/
def quadGapIndex {n : Nat} (a b c d x : Fin n) : Fin 4 :=
  if a < x ∧ x < b then 0 else if b < x ∧ x < c then 1
  else if c < x ∧ x < d then 2 else 3

abbrev QuadRemainder {n : Nat} (a b c d : Fin n) :=
  {x : Fin n // x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d}

def remainderGapIndex {n : Nat} (a b c d : Fin n)
    (x : QuadRemainder a b c d) : Fin 4 := quadGapIndex a b c d x.val

set_option maxHeartbeats 800000 in
theorem quadGapIndex_noncrossing {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    IsNoncrossing (Setoid.ker (quadGapIndex a b c d)) := by
  intro w x y z hwx hxy hyz hwy hxz
  simp only [Setoid.ker_def, quadGapIndex] at hwy hxz ⊢
  split_ifs at * <;> omega

theorem remainderGapIndex_noncrossing {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    IsNoncrossing (Setoid.ker (remainderGapIndex a b c d)) := by
  intro w x y z hwx hxy hyz hwy hxz
  exact quadGapIndex_noncrossing a b c d hab hbc hcd
    w.val x.val y.val z.val hwx hxy hyz hwy hxz

/-- Removing the four endpoints from the two adjacent chord barriers gives
exactly the regional partition that isolates gaps 0 and 2. -/
theorem adjacent_pair_remainder_regions {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Setoid.comap (fun x : QuadRemainder a b c d => x.val)
      (pairGapPartition a b ⊓ pairGapPartition c d) =
      adjacentGapRegions (remainderGapIndex a b c d) := by
  apply Setoid.ext
  intro x y
  obtain ⟨hxa,hxb,hxc,hxd⟩ := x.property
  obtain ⟨hya,hyb,hyc,hyd⟩ := y.property
  simp only [Setoid.comap_rel, Setoid.inf_iff_and, pairGapPartition,
    adjacentGapRegions, Setoid.ker_def, Function.comp_apply,
    remainderGapIndex, quadGapIndex]
  simp only [hxa,hxb,hxc,hxd,hya,hyb,hyc,hyd,or_self,if_false]
  have h0 : adjacentGapLabel 0 = 0 := rfl
  have h1 : adjacentGapLabel 1 = 1 := rfl
  have h2 : adjacentGapLabel 2 = 2 := rfl
  have h3 : adjacentGapLabel 3 = 1 := rfl
  split_ifs <;> simp only [h0,h1,h2,h3,and_self,iff_self] <;> omega

/-- The nested chord barriers isolate gaps 1 and 3 and join gaps 0 and 2. -/
theorem nested_pair_remainder_regions {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Setoid.comap (fun x : QuadRemainder a b c d => x.val)
      (pairGapPartition a d ⊓ pairGapPartition b c) =
      nestedGapRegions (remainderGapIndex a b c d) := by
  apply Setoid.ext
  intro x y
  obtain ⟨hxa,hxb,hxc,hxd⟩ := x.property
  obtain ⟨hya,hyb,hyc,hyd⟩ := y.property
  simp only [Setoid.comap_rel, Setoid.inf_iff_and, pairGapPartition,
    nestedGapRegions, Setoid.ker_def, Function.comp_apply,
    remainderGapIndex, quadGapIndex]
  simp only [hxa,hxb,hxc,hxd,hya,hyb,hyc,hyd,or_self,if_false]
  have h0 : nestedGapLabel 0 = 0 := rfl
  have h1 : nestedGapLabel 1 = 1 := rfl
  have h2 : nestedGapLabel 2 = 0 := rfl
  have h3 : nestedGapLabel 3 = 3 := rfl
  split_ifs <;> simp only [h0,h1,h2,h3,and_self,iff_self] <;> omega

theorem forced_adjacent_pairs_remainder_refines {n : Nat}
    (r : Setoid (Fin n)) (hr : IsNoncrossing r) (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hp : IsPairBlock r a b) (hq : IsPairBlock r c d) :
    Setoid.comap (fun x : QuadRemainder a b c d => x.val) r ≤
      adjacentGapRegions (remainderGapIndex a b c d) := by
  rw [← adjacent_pair_remainder_regions a b c d hab hbc hcd]
  intro x y h
  exact ⟨forced_pair_refines_gaps r hr a b hp h,
    forced_pair_refines_gaps r hr c d hq h⟩

theorem forced_nested_pairs_remainder_refines {n : Nat}
    (r : Setoid (Fin n)) (hr : IsNoncrossing r) (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hp : IsPairBlock r a d) (hq : IsPairBlock r b c) :
    Setoid.comap (fun x : QuadRemainder a b c d => x.val) r ≤
      nestedGapRegions (remainderGapIndex a b c d) := by
  rw [← nested_pair_remainder_regions a b c d hab hbc hcd]
  intro x y h
  exact ⟨forced_pair_refines_gaps r hr a d hp h,
    forced_pair_refines_gaps r hr b c hq h⟩

/-- Four-gap intersection for arbitrary ordered endpoints, including a cyclic
exterior gap containing both a prefix and a suffix. -/
theorem positional_four_gap_intersection {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d)) :
    (WitnessUnder
        (Setoid.comap (fun x : QuadRemainder a b c d => x.val)
          (pairGapPartition a b ⊓ pairGapPartition c d)) p ∧
      WitnessUnder
        (Setoid.comap (fun x : QuadRemainder a b c d => x.val)
          (pairGapPartition a d ⊓ pairGapPartition b c)) p) ↔
      WitnessUnder (Setoid.ker (remainderGapIndex a b c d)) p := by
  rw [adjacent_pair_remainder_regions a b c d hab hbc hcd,
    nested_pair_remainder_regions a b c d hab hbc hcd]
  exact four_gap_witness_intersection _ (remainderGapIndex_noncrossing a b c d hab hbc hcd) p

end LC004
