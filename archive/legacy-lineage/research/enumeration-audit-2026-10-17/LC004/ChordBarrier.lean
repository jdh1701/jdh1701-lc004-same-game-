import LC004.NoncrossingRestriction

namespace LC004

/-- A noncrossing block disjoint from the endpoints of a chord cannot have
one position strictly inside the chord and another outside it. -/
theorem noncrossing_interval_barrier {α : Type*} [LinearOrder α]
    (r : Setoid α) (hr : IsNoncrossing r) (a b x y : α)
    (hab : r a b) (hxy : r x y) (hax : ¬r a x) (hay : ¬r a y) :
    (a < x ∧ x < b) ↔ (a < y ∧ y < b) := by
  classical
  have forward : ∀ x y, r x y → ¬r a x → ¬r a y →
      (a < x ∧ x < b) → (a < y ∧ y < b) := by
    intro x y hxy hax hay hx
    constructor
    · by_contra h
      have hya : y ≤ a := le_of_not_gt h
      rcases lt_or_eq_of_le hya with hya | rfl
      · have hyra := hr y a x b hya hx.1 hx.2 (r.symm hxy) hab
        exact hay (r.symm hyra)
      · exact hay (r.refl _)
    · by_contra h
      have hby : b ≤ y := le_of_not_gt h
      rcases lt_or_eq_of_le hby with hby | rfl
      · exact hax (hr a x b y hx.1 hx.2 hby hab hxy)
      · exact hay hab
  exact ⟨forward x y hxy hax hay,forward y x (r.symm hxy) hay hax⟩

#print axioms noncrossing_interval_barrier

end LC004
