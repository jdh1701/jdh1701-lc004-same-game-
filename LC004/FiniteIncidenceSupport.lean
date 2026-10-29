import Mathlib

namespace LC004
open scoped BigOperators Classical

/-- Lower incidence transform on a finite partially ordered set. -/
noncomputable def lowerIncidence {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → Int) (p : α) : Int := by
  classical
  exact ∑ q, if q ≤ p then f q else 0

theorem lowerIncidence_injective {α : Type*} [Fintype α] [PartialOrder α] :
    Function.Injective (@lowerIncidence α _ _) := by
  classical
  intro f g h
  funext p
  have wf : WellFounded ((· < ·) : α → α → Prop) := wellFounded_lt
  induction p using wf.induction with
  | h p ih =>
    have hz : lowerIncidence (fun q => f q - g q) p = 0 := by
      have hp := congrFun h p
      unfold lowerIncidence at *
      rw [← sub_eq_zero] at hp
      rw [← Finset.sum_sub_distrib] at hp
      calc
        _ = ∑ q, ((if q ≤ p then f q else 0) -
            (if q ≤ p then g q else 0)) := by
          apply Finset.sum_congr rfl
          intro q _
          split_ifs <;> simp
        _ = 0 := hp
    have he : lowerIncidence (fun q => f q - g q) p = f p - g p := by
      unfold lowerIncidence
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hqp
        by_cases hle : q ≤ p
        · simp [hle, ih q (lt_of_le_of_ne hle hqp)]
        · simp [hle]
      · simp
    rw [he] at hz
    exact sub_eq_zero.mp hz

/-- If the lower transform only sees meet with rho, all coefficients outside
the principal ideal of rho vanish. This is the support step of gap inversion. -/
theorem incidence_support_of_meet_invariance {α : Type*} [Fintype α]
    [SemilatticeInf α] (f : α → Int) (rho : α)
    (h : ∀ p, lowerIncidence f p = lowerIncidence f (p ⊓ rho))
    (p : α) (hp : ¬ p ≤ rho) : f p = 0 := by
  classical
  let g : α → Int := fun q => if q ≤ rho then f q else 0
  have hg : lowerIncidence f = lowerIncidence g := by
    funext r
    rw [h r]
    unfold lowerIncidence
    apply Finset.sum_congr rfl
    intro q _
    by_cases hqr : q ≤ r <;> by_cases hq : q ≤ rho <;>
      simp [g, le_inf_iff, hqr, hq]
  have he := congrFun (lowerIncidence_injective hg) p
  simpa [g, hp] using he

#print axioms lowerIncidence_injective
#print axioms incidence_support_of_meet_invariance

theorem lowerIncidence_truncate {α : Type*} [Fintype α] [SemilatticeInf α]
    (f : α → Int) (rho r : α) :
    lowerIncidence (fun q => if q ≤ rho then f q else 0) r =
      lowerIncidence f (r ⊓ rho) := by
  classical
  unfold lowerIncidence
  apply Finset.sum_congr rfl
  intro q _
  by_cases hqr : q ≤ r <;> by_cases hq : q ≤ rho <;>
    simp [le_inf_iff,hqr,hq]

/-- Local version: invariance only needs to hold below the partition whose
coefficient is being computed. This avoids assuming a global game invariance. -/
theorem incidence_support_of_local_meet_invariance {α : Type*} [Fintype α]
    [SemilatticeInf α] (f : α → Int) (rho p : α)
    (h : ∀ r, r ≤ p → lowerIncidence f r = lowerIncidence f (r ⊓ rho))
    (hp : ¬ p ≤ rho) : f p = 0 := by
  classical
  let g : α → Int := fun q => if q ≤ p then f q else 0
  have hg : ∀ r, lowerIncidence g r = lowerIncidence g (r ⊓ rho) := by
    intro r
    simp only [g,lowerIncidence_truncate]
    rw [h (r ⊓ p) inf_le_right]
    congr 1
    exact inf_right_comm r p rho
  have hz := incidence_support_of_meet_invariance g rho hg p hp
  simpa [g] using hz

#print axioms lowerIncidence_truncate
#print axioms incidence_support_of_local_meet_invariance
end LC004
