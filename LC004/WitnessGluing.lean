import LC004.PairGapDecomposition

namespace LC004

/-- Use `r` on the selected positions and `s` on the other positions. -/
def splicePartitions {α : Type*} (r s : Setoid α) (U : α → Prop)
    [DecidablePred U] : Setoid α where
  r x y := (U x ↔ U y) ∧ if U x then r x y else s x y
  iseqv := {
    refl := by intro x; exact ⟨Iff.rfl, by split <;> first | exact r.refl x | exact s.refl x⟩
    symm := by
      intro x y h
      refine ⟨h.1.symm, ?_⟩
      by_cases hx : U x
      · simpa [h.1.mp hx] using r.symm (by simpa [hx] using h.2)
      · have hy : ¬U y := fun hy => hx (h.1.mpr hy)
        simpa [hy] using s.symm (by simpa [hx] using h.2)
    trans := by
      intro x y z hxy hyz
      refine ⟨hxy.1.trans hyz.1, ?_⟩
      by_cases hx : U x
      · have hy := hxy.1.mp hx
        simpa [hx] using r.trans (by simpa [hx] using hxy.2) (by simpa [hy] using hyz.2)
      · have hy : ¬U y := fun hy => hx (hxy.1.mpr hy)
        simpa [hx] using s.trans (by simpa [hx] using hxy.2) (by simpa [hy] using hyz.2) }

theorem splicePartitions_left {α : Type*} (r s : Setoid α) (U : α → Prop)
    [DecidablePred U] (hr : ∀ x y, r x y → (U x ↔ U y))
    (x y : α) (hx : U x) : splicePartitions r s U x y ↔ r x y := by
  change ((U x ↔ U y) ∧ if U x then r x y else s x y) ↔ r x y
  simp only [if_pos hx]
  exact ⟨And.right, fun h => ⟨hr x y h,h⟩⟩

theorem splicePartitions_right {α : Type*} (r s : Setoid α) (U : α → Prop)
    [DecidablePred U] (hs : ∀ x y, s x y → (U x ↔ U y))
    (x y : α) (hx : ¬U x) : splicePartitions r s U x y ↔ s x y := by
  change ((U x ↔ U y) ∧ if U x then r x y else s x y) ↔ s x y
  simp only [if_neg hx]
  exact ⟨And.right, fun h => ⟨hs x y h,h⟩⟩

/-- Splicing preserves entire source blocks when each source preserves the
selector. If the result refines a noncrossing barrier, it is a witness. -/
theorem splicePartitions_pairTriple {α : Type*} [LinearOrder α] [Finite α]
    (r s g : Setoid α) (U : α → Prop) [DecidablePred U]
    (hr : PairTriplePartition r) (hs : PairTriplePartition s)
    (hrU : ∀ x y, r x y → (U x ↔ U y))
    (hsU : ∀ x y, s x y → (U x ↔ U y))
    (hg : IsNoncrossing g) (hgU : ∀ x y, g x y → (U x ↔ U y))
    (hle : splicePartitions r s U ≤ g) :
    PairTriplePartition (splicePartitions r s U) := by
  classical
  let t := splicePartitions r s U
  have hleft (x : α) (hx : U x) : partitionBlockSize t x = partitionBlockSize r x := by
    apply @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
    exact {
      toFun := fun y => ⟨y.val, r.symm ((splicePartitions_left r s U hrU x y.val hx).mp
        (t.symm y.property))⟩
      invFun := fun y => ⟨y.val, t.symm ((splicePartitions_left r s U hrU x y.val hx).mpr
        (r.symm y.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hright (x : α) (hx : ¬U x) : partitionBlockSize t x = partitionBlockSize s x := by
    apply @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
    exact {
      toFun := fun y => ⟨y.val, s.symm ((splicePartitions_right r s U hsU x y.val hx).mp
        (t.symm y.property))⟩
      invFun := fun y => ⟨y.val, t.symm ((splicePartitions_right r s U hsU x y.val hx).mpr
        (s.symm y.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · intro a b c d hab hbc hcd hac hbd
    have hgab := hg a b c d hab hbc hcd (hle hac) (hle hbd)
    have huab := hgU a b hgab
    by_cases ha : U a
    · have hb := huab.mp ha
      exact (splicePartitions_left r s U hrU a b ha).mpr
        (hr.1 a b c d hab hbc hcd
          ((splicePartitions_left r s U hrU a c ha).mp hac)
          ((splicePartitions_left r s U hrU b d hb).mp hbd))
    · have hb : ¬U b := fun hb => ha (huab.mpr hb)
      exact (splicePartitions_right r s U hsU a b ha).mpr
        (hs.1 a b c d hab hbc hcd
          ((splicePartitions_right r s U hsU a c ha).mp hac)
          ((splicePartitions_right r s U hsU b d hb).mp hbd))
  · intro x
    by_cases hx : U x
    · change partitionBlockSize t x = 2 ∨ partitionBlockSize t x = 3
      rw [hleft x hx]
      exact hr.2 x
    · change partitionBlockSize t x = 2 ∨ partitionBlockSize t x = 3
      rw [hright x hx]
      exact hs.2 x

/-- Coverage by noncrossing pair/triple witnesses refining the supplied barrier. -/
def WitnessUnder {α : Type*} [LinearOrder α] [Finite α]
    (A p : Setoid α) : Prop :=
  ∃ r, PairTriplePartition r ∧ r ≤ A ∧ r ≤ p

/-- Two complementary regional witness families intersect exactly in the
family constrained by their common gap barrier. The forward direction
constructs a witness by retaining whole blocks from the two given witnesses. -/
theorem witness_intersection_glue {α : Type*} [LinearOrder α] [Finite α]
    (A B g : Setoid α) (U : α → Prop) [DecidablePred U]
    (hg : IsNoncrossing g) (hgA : g ≤ A) (hgB : g ≤ B)
    (hAU : ∀ x y, A x y → (U x ↔ U y))
    (hBU : ∀ x y, B x y → (U x ↔ U y))
    (hAg : ∀ x y, U x → A x y → g x y)
    (hBg : ∀ x y, ¬U x → B x y → g x y)
    (p : Setoid α) :
    (WitnessUnder A p ∧ WitnessUnder B p) ↔ WitnessUnder g p := by
  constructor
  · rintro ⟨⟨r,hr,hrA,hrp⟩,⟨s,hs,hsB,hsp⟩⟩
    let t := splicePartitions r s U
    have hrU : ∀ x y, r x y → (U x ↔ U y) := fun x y h => hAU x y (hrA h)
    have hsU : ∀ x y, s x y → (U x ↔ U y) := fun x y h => hBU x y (hsB h)
    have htg : t ≤ g := by
      intro x y h
      by_cases hx : U x
      · exact hAg x y hx (hrA ((splicePartitions_left r s U hrU x y hx).mp h))
      · exact hBg x y hx (hsB ((splicePartitions_right r s U hsU x y hx).mp h))
    refine ⟨t, splicePartitions_pairTriple r s g U hr hs hrU hsU hg
      (fun x y h => hAU x y (hgA h)) htg, htg, ?_⟩
    intro x y h
    by_cases hx : U x
    · exact hrp ((splicePartitions_left r s U hrU x y hx).mp h)
    · exact hsp ((splicePartitions_right r s U hsU x y hx).mp h)
  · rintro ⟨r,hr,hrg,hrp⟩
    exact ⟨⟨r,hr,le_trans hrg hgA,hrp⟩,⟨r,hr,le_trans hrg hgB,hrp⟩⟩

end LC004
