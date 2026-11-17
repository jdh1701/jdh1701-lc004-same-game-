import LC004.ColorPatternSpace
import Mathlib

namespace LC004
open scoped BigOperators Classical

/-- Identifying colors preserves the existence of a winning certificate. -/
theorem winning_pattern_upward_closed {n : Nat} {p q : ColorPattern n}
    (hpq : p ≤ q) (hp : WinningColorPattern p) : WinningColorPattern q := by
  obtain ⟨cert⟩ := hp
  refine ⟨cert.recolor (patternColor q) ?_⟩
  intro i j hij
  exact (patternColor_eq_iff q i j).mpr (hpq ((patternColor_eq_iff p i j).mp hij))

noncomputable def constraintIndicator {n : Nat} (p r : ColorPattern n) : Int :=
  if p ≤ r then 1 else 0

theorem constraintIndicator_join {n : Nat} (p q r : ColorPattern n) :
    constraintIndicator (p ⊔ q) r = constraintIndicator p r * constraintIndicator q r := by
  classical
  by_cases hp : p ≤ r <;> by_cases hq : q ≤ r <;>
    simp [constraintIndicator, sup_le_iff, hp, hq]

/-- A single inclusion-exclusion update can be computed entirely through
joins of equality constraints. Equal joins may subsequently be collected. -/
theorem constraint_join_union_update {n : Nat} (s : Finset (ColorPattern n))
    (weight : ColorPattern n → Int) (c r : ColorPattern n) (P : Prop)
    [Decidable P]
    (hscore : (∑ p ∈ s, weight p * constraintIndicator p r) = if P then 1 else 0) :
    (∑ p ∈ s, weight p * constraintIndicator p r) + constraintIndicator c r -
      (∑ p ∈ s, weight p * constraintIndicator (p ⊔ c) r) =
        if P ∨ c ≤ r then 1 else 0 := by
  classical
  have hinter : (∑ p ∈ s, weight p * constraintIndicator (p ⊔ c) r) =
      (∑ p ∈ s, weight p * constraintIndicator p r) * constraintIndicator c r := by
    simp only [constraintIndicator_join, ← mul_assoc, Finset.sum_mul]
  rw [hinter, hscore]
  by_cases hp : P <;> by_cases hc : c ≤ r <;>
    simp [constraintIndicator, hp, hc]

#print axioms winning_pattern_upward_closed
#print axioms constraint_join_union_update
end LC004
