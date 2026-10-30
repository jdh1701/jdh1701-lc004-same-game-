import LC004.MixedFiveSixCertificates

namespace LC004
open scoped Classical

/-- A bounded path certificate is sufficient to prove an actual setoid join. -/
theorem setoid_sup_eq_of_three_steps {α : Type*} (a b r : Setoid α)
    (ha : a ≤ r) (hb : b ≤ r)
    (hpath : ∀ u v, r u v → ∃ w z,
      (a u w ∨ b u w) ∧ (a w z ∨ b w z) ∧ (a z v ∨ b z v)) : a ⊔ b = r := by
  apply le_antisymm (sup_le ha hb)
  intro u v huv
  obtain ⟨w,z,huw,hwz,hzv⟩ := hpath u v huv
  have step : ∀ x y, a x y ∨ b x y → (a ⊔ b) x y := by
    intro x y h
    exact h.elim (fun h => (show a ≤ a ⊔ b from le_sup_left) h)
      (fun h => (show b ≤ a ⊔ b from le_sup_right) h)
  exact (a ⊔ b).trans (step u w huw) ((a ⊔ b).trans (step w z hwz) (step z v hzv))

abbrev mixed56A := mixed56Encoded 2 4
abbrev mixed56B := mixed56Encoded 2 6
abbrev mixed56C := mixed56Encoded 1 0

def mixed56BarrierColor : Fin 11 → Fin 4 := ![0,0,1,2,2,3,3,2,1,1,1]
def mixed56Barrier : ColorPattern 11 := Setoid.ker mixed56BarrierColor

theorem mixed56_ab_barrier : mixed56A ≤ mixed56Barrier ∧ mixed56B ≤ mixed56Barrier := by
  change (∀ u v, mixed56Color 2 4 u = mixed56Color 2 4 v → mixed56BarrierColor u = mixed56BarrierColor v) ∧
    (∀ u v, mixed56Color 2 6 u = mixed56Color 2 6 v → mixed56BarrierColor u = mixed56BarrierColor v)
  decide +kernel

theorem mixed56_not_le_barrier : ¬ mixed56Pattern ≤ mixed56Barrier := by
  change ¬ (∀ u v, mixed56BaseColor u = mixed56BaseColor v → mixed56BarrierColor u = mixed56BarrierColor v)
  decide +kernel

theorem mixed56_ab_ne : mixed56A ⊔ mixed56B ≠ mixed56Pattern := by
  intro he
  apply mixed56_not_le_barrier
  rw [← he]
  exact sup_le mixed56_ab_barrier.1 mixed56_ab_barrier.2

theorem mixed56_join_ac : mixed56A ⊔ mixed56C = mixed56Pattern := by
  apply setoid_sup_eq_of_three_steps _ _ _ (mixed56_encoded_refines 2 4) (mixed56_encoded_refines 1 0)
  change ∀ u v, mixed56BaseColor u = mixed56BaseColor v → ∃ w z : Fin 11,
    (mixed56Color 2 4 u = mixed56Color 2 4 w ∨ mixed56Color 1 0 u = mixed56Color 1 0 w) ∧
    (mixed56Color 2 4 w = mixed56Color 2 4 z ∨ mixed56Color 1 0 w = mixed56Color 1 0 z) ∧
    (mixed56Color 2 4 z = mixed56Color 2 4 v ∨ mixed56Color 1 0 z = mixed56Color 1 0 v)
  decide +kernel

theorem mixed56_join_bc : mixed56B ⊔ mixed56C = mixed56Pattern := by
  apply setoid_sup_eq_of_three_steps _ _ _ (mixed56_encoded_refines 2 6) (mixed56_encoded_refines 1 0)
  change ∀ u v, mixed56BaseColor u = mixed56BaseColor v → ∃ w z : Fin 11,
    (mixed56Color 2 6 u = mixed56Color 2 6 w ∨ mixed56Color 1 0 u = mixed56Color 1 0 w) ∧
    (mixed56Color 2 6 w = mixed56Color 2 6 z ∨ mixed56Color 1 0 w = mixed56Color 1 0 z) ∧
    (mixed56Color 2 6 z = mixed56Color 2 6 v ∨ mixed56Color 1 0 z = mixed56Color 1 0 v)
  decide +kernel

theorem mixed56_generators_ne_base : mixed56A ≠ mixed56Pattern ∧
    mixed56B ≠ mixed56Pattern ∧ mixed56C ≠ mixed56Pattern := by
  have ha : ¬ (∀ u v, mixed56Color 2 4 u = mixed56Color 2 4 v ↔ mixed56BaseColor u = mixed56BaseColor v) := by decide +kernel
  have hb : ¬ (∀ u v, mixed56Color 2 6 u = mixed56Color 2 6 v ↔ mixed56BaseColor u = mixed56BaseColor v) := by decide +kernel
  have hc : ¬ (∀ u v, mixed56Color 1 0 u = mixed56Color 1 0 v ↔ mixed56BaseColor u = mixed56BaseColor v) := by decide +kernel
  exact ⟨fun h => ha (Setoid.ext_iff.mp h),fun h => hb (Setoid.ext_iff.mp h),fun h => hc (Setoid.ext_iff.mp h)⟩

/-- Three complete original certificate generators do NOT cancel in this mixed
profile. This is an original-game coefficient, not just a CSP or face-sum model. -/
theorem winningJoinCoefficient_mixed56 : winningJoinCoefficient 11 mixed56Pattern = -1 := by
  rw [winningJoinCoefficient_eq_local_generators mixed56Pattern mixed56Generators mixed56_generators_complete]
  have hba : mixed56B ⊔ mixed56A ≠ mixed56Pattern := by simpa only [sup_comm] using mixed56_ab_ne
  have hca : mixed56C ⊔ mixed56A = mixed56Pattern := by simpa only [sup_comm] using mixed56_join_ac
  have hcb : mixed56C ⊔ mixed56B = mixed56Pattern := by simpa only [sup_comm] using mixed56_join_bc
  have htriple : (mixed56C ⊔ mixed56B) ⊔ mixed56A = mixed56Pattern := by
    rw [hcb,sup_eq_left.mpr (mixed56_encoded_refines 2 4)]
  have hA : mixed56A ≤ mixed56Pattern := mixed56_encoded_refines 2 4
  simp [mixed56Generators,certificateJoinTerms,collectedJoinCoefficient,
    mixed56_generators_ne_base.1,mixed56_generators_ne_base.2.1,
    mixed56_generators_ne_base.2.2,hba,hca,hcb,htriple,hA]

theorem mixed56_generators_distinct : mixed56A ≠ mixed56B ∧
    mixed56A ≠ mixed56C ∧ mixed56B ≠ mixed56C := by
  have ha : ¬ (∀ u v, mixed56Color 2 4 u = mixed56Color 2 4 v ↔ mixed56Color 2 6 u = mixed56Color 2 6 v) := by decide +kernel
  have hb : ¬ (∀ u v, mixed56Color 2 4 u = mixed56Color 2 4 v ↔ mixed56Color 1 0 u = mixed56Color 1 0 v) := by decide +kernel
  have hc : ¬ (∀ u v, mixed56Color 2 6 u = mixed56Color 2 6 v ↔ mixed56Color 1 0 u = mixed56Color 1 0 v) := by decide +kernel
  exact ⟨fun h => ha (Setoid.ext_iff.mp h),fun h => hb (Setoid.ext_iff.mp h),fun h => hc (Setoid.ext_iff.mp h)⟩

theorem mixed56_original_generator_count :
    (Finset.univ.filter (fun c : ColorPattern 11 => CertificateConstraint c ∧ c ≤ mixed56Pattern)).card = 3 := by
  have he : Finset.univ.filter (fun c : ColorPattern 11 => CertificateConstraint c ∧ c ≤ mixed56Pattern) =
      {mixed56A,mixed56B,mixed56C} := by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mixed56_generators_complete,
      mixed56Generators,List.mem_cons,List.mem_nil_iff,or_false,Finset.mem_insert,Finset.mem_singleton]
  rw [he]
  simp [mixed56_generators_distinct.1,mixed56_generators_distinct.2.1,mixed56_generators_distinct.2.2]

/-- Explicit original-game refutation of extending three-generator cancellation
from all-five profiles to arbitrary heavy profiles. -/
theorem three_generator_cancellation_fails_for_mixed_profiles :
    ∃ p : ColorPattern 11,
      (Finset.univ.filter (fun c : ColorPattern 11 => CertificateConstraint c ∧ c ≤ p)).card = 3 ∧
      winningJoinCoefficient 11 p ≠ 0 := by
  exact ⟨mixed56Pattern,mixed56_original_generator_count,by rw [winningJoinCoefficient_mixed56]; decide⟩

#print axioms winningJoinCoefficient_mixed56
#print axioms three_generator_cancellation_fails_for_mixed_profiles
end LC004
