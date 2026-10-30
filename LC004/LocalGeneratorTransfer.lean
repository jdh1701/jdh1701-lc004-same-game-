import LC004.IncidenceFaceSum

namespace LC004
open scoped Classical

/-- Equality of lower incidence on one principal ideal determines the coefficient
at its top. Values outside that ideal need not agree. -/
theorem coefficient_eq_of_incidence_eq_below {α : Type*} [Fintype α]
    [SemilatticeInf α] (f g : α → Int) (p : α)
    (h : ∀ r, r ≤ p → lowerIncidence f r = lowerIncidence g r) : f p = g p := by
  have he : (fun r => if r ≤ p then f r else 0) =
      (fun r => if r ≤ p then g r else 0) := by
    apply lowerIncidence_injective
    funext r
    rw [lowerIncidence_truncate,lowerIncidence_truncate]
    exact h (r ⊓ p) inf_le_right
  simpa only [le_refl,if_true] using congrFun he p

/-- A complete LOCAL list of original certificate generators suffices to compute
one original coefficient. No enumeration of every pattern on the board is needed. -/
theorem winningJoinCoefficient_eq_local_generators {n : Nat} (p : ColorPattern n)
    (cs : List (ColorPattern n))
    (hcs : ∀ c, CertificateConstraint c ∧ c ≤ p ↔ c ∈ cs) :
    winningJoinCoefficient n p = collectedJoinCoefficient (certificateJoinTerms cs) p := by
  apply coefficient_eq_of_incidence_eq_below
  intro r hrp
  rw [winningJoinCoefficient_incidence,collectedJoinCoefficient_incidence,
    certificateJoinTerms_score]
  have he : WinningColorPattern r ↔ ∃ c ∈ cs, c ≤ r := by
    rw [winning_iff_constraint_refinement]
    constructor
    · rintro ⟨c,hc,hcr⟩
      exact ⟨c,(hcs c).mp ⟨hc,hcr.trans hrp⟩,hcr⟩
    · rintro ⟨c,hc,hcr⟩
      exact ⟨c,((hcs c).mpr hc).1,hcr⟩
  simp only [he]

/-- A common proper refinement of every certificate is a coefficient obstruction.
This applies to arbitrary class-size profiles. -/
theorem winningJoinCoefficient_zero_of_common_refinement {n : Nat}
    (p rho : ColorPattern n) (hsep : ¬ p ≤ rho)
    (hcommon : ∀ c, CertificateConstraint c → c ≤ p → c ≤ rho) :
    winningJoinCoefficient n p = 0 := by
  apply incidence_support_of_local_meet_invariance (winningJoinCoefficient n) rho p
  · intro r hrp
    simp only [winningJoinCoefficient_incidence]
    have he : WinningColorPattern r ↔ WinningColorPattern (r ⊓ rho) := by
      rw [winning_iff_constraint_refinement,winning_iff_constraint_refinement]
      constructor
      · rintro ⟨c,hc,hcr⟩
        exact ⟨c,hc,le_inf hcr (hcommon c hc (hcr.trans hrp))⟩
      · rintro ⟨c,hc,hcr⟩
        exact ⟨c,hc,hcr.trans inf_le_left⟩
    simp only [he]
  · exact hsep

#print axioms winningJoinCoefficient_eq_local_generators
#print axioms winningJoinCoefficient_zero_of_common_refinement
end LC004
