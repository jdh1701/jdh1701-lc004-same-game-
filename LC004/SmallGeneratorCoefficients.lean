import LC004.LocalGeneratorTransfer

namespace LC004
open scoped Classical

/-- A complete pair of proper original generators with top join contributes -1. -/
theorem winningJoinCoefficient_two_generators {n : Nat} (p a b : ColorPattern n)
    (hcs : ∀ c, CertificateConstraint c ∧ c ≤ p ↔ c ∈ [a,b])
    (ha : a ≠ p) (hb : b ≠ p) (hab : a ⊔ b = p) :
    winningJoinCoefficient n p = -1 := by
  rw [winningJoinCoefficient_eq_local_generators p [a,b] hcs]
  have hba : b ⊔ a = p := by simpa only [sup_comm] using hab
  simp [certificateJoinTerms,collectedJoinCoefficient,ha,hb,hba]

/-- A complete triple with exactly two top-joining pairs also contributes -1.
The family need not have an all-five profile. -/
theorem winningJoinCoefficient_three_generators_two_top_pairs {n : Nat}
    (p a b c : ColorPattern n)
    (hcs : ∀ d, CertificateConstraint d ∧ d ≤ p ↔ d ∈ [a,b,c])
    (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ p)
    (hab : a ⊔ b ≠ p) (hac : a ⊔ c = p) (hbc : b ⊔ c = p) :
    winningJoinCoefficient n p = -1 := by
  rw [winningJoinCoefficient_eq_local_generators p [a,b,c] hcs]
  have hba : b ⊔ a ≠ p := by simpa only [sup_comm] using hab
  have hca : c ⊔ a = p := by simpa only [sup_comm] using hac
  have hcb : c ⊔ b = p := by simpa only [sup_comm] using hbc
  have hle : a ≤ p := ((hcs a).mpr (by simp)).2
  have htriple : (c ⊔ b) ⊔ a = p := by rw [hcb,sup_eq_left.mpr hle]
  simp [certificateJoinTerms,collectedJoinCoefficient,ha,hb,hc,hba,hca,hcb,htriple,hle]

#print axioms winningJoinCoefficient_two_generators
#print axioms winningJoinCoefficient_three_generators_two_top_pairs
end LC004
