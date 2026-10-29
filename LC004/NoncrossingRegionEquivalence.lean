import LC004.OrderedCertificateAssembly

namespace LC004

/-- The forward half of arbitrary noncrossing-region decomposition: closure
under original color equality ensures every certificate block stays inside. -/
theorem winning_restrict_closed_color_region {n m : Nat} (p : ColorPattern n)
    (e : Fin m ↪o Fin n) (hsat : ∀ i b, p (e i) b → ∃ j, e j = b)
    (hwin : WinningColorPattern p) : WinningColorPattern (restrictColorPattern p e) := by
  obtain ⟨c,hc,hcp⟩ := (winning_iff_constraint_refinement p).mp hwin
  apply (winning_iff_constraint_refinement _).mpr
  exact ⟨restrictColorPattern c e,
    certificateConstraint_restrict c hc e (fun i b h => hsat i b (hcp h)),
    restrictColorPattern_mono hcp e⟩

/-- Exact winning-indicator factorization for a color-saturated disjoint
noncrossing cover. This is the game input to NC-component coefficient factoring. -/
theorem winning_iff_noncrossing_region_cover {n : Nat} {ι : Type*}
    (p : ColorPattern n) (m : ι → Nat) (e : ∀ k, Fin (m k) ↪o Fin n)
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l)
    (noncrossing : ∀ k l i j s t,
      e k i < e l s → e l s < e k j → e k j < e l t → k = l)
    (saturated : ∀ k i b, p (e k i) b → ∃ j, e k j = b) :
    WinningColorPattern p ↔ ∀ k, WinningColorPattern (restrictColorPattern p (e k)) := by
  exact ⟨fun h k => winning_restrict_closed_color_region p (e k) (saturated k) h,
    winning_of_ordered_region_cover p m e cover disjoint noncrossing⟩

#print axioms winning_restrict_closed_color_region
#print axioms winning_iff_noncrossing_region_cover
end LC004
