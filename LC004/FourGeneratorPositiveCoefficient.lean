import LC004.SmallGeneratorCoefficients

namespace LC004
open scoped Classical

/-- Four complete proper generators with just the two disjoint top-joining
pairs have coefficient +1. This is conditional and asserts no such pattern
exists in any particular size profile. -/
theorem winningJoinCoefficient_four_generators_two_disjoint_top_pairs {n : Nat}
    (p a b c d : ColorPattern n)
    (hcs : ∀ e, CertificateConstraint e ∧ e ≤ p ↔ e ∈ [a,b,c,d])
    (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ p) (hd : d ≠ p)
    (hab : a ⊔ b ≠ p) (hac : a ⊔ c ≠ p) (had : a ⊔ d = p)
    (hbc : b ⊔ c = p) (hbd : b ⊔ d ≠ p) (hcd : c ⊔ d ≠ p) :
    winningJoinCoefficient n p = 1 := by
  rw [winningJoinCoefficient_eq_local_generators p [a,b,c,d] hcs]
  have hA : a ≤ p := ((hcs a).mpr (by simp)).2
  have hB : b ≤ p := ((hcs b).mpr (by simp)).2
  have hC : c ≤ p := ((hcs c).mpr (by simp)).2
  have hD : d ≤ p := ((hcs d).mpr (by simp)).2
  have hba : b ⊔ a ≠ p := by simpa only [sup_comm] using hab
  have hca : c ⊔ a ≠ p := by simpa only [sup_comm] using hac
  have hda : d ⊔ a = p := by simpa only [sup_comm] using had
  have hcb : c ⊔ b = p := by simpa only [sup_comm] using hbc
  have hdb : d ⊔ b ≠ p := by simpa only [sup_comm] using hbd
  have hdc : d ⊔ c ≠ p := by simpa only [sup_comm] using hcd
  have hcba : (c ⊔ b) ⊔ a = p := by rw [hcb,sup_eq_left.mpr hA]
  have hdba : (d ⊔ b) ⊔ a = p := by
    calc
      _ = (d ⊔ a) ⊔ b := by ac_rfl
      _ = p := by rw [hda,sup_eq_left.mpr hB]
  have hdca : (d ⊔ c) ⊔ a = p := by
    calc
      _ = (d ⊔ a) ⊔ c := by ac_rfl
      _ = p := by rw [hda,sup_eq_left.mpr hC]
  have hdcb : (d ⊔ c) ⊔ b = p := by
    calc
      _ = (c ⊔ b) ⊔ d := by ac_rfl
      _ = p := by rw [hcb,sup_eq_left.mpr hD]
  have hdcba : ((d ⊔ c) ⊔ b) ⊔ a = p := by rw [hdcb,sup_eq_left.mpr hA]
  simp [certificateJoinTerms,collectedJoinCoefficient,ha,hb,hc,hd,
    hba,hca,hda,hcb,hdb,hdc,hcba,hdba,hdca,hdcb,hdcba]

#print axioms winningJoinCoefficient_four_generators_two_disjoint_top_pairs
end LC004
