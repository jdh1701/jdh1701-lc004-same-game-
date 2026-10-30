import LC004.ColorPatternSpace
import Mathlib

namespace LC004

/-- Coarsenings are exactly equivalence relations on the original color classes. -/
def patternCoarseningEquiv {n : Nat} (p : ColorPattern n) :
    {r : ColorPattern n // p ≤ r} ≃ Setoid (Quotient p) :=
  (Setoid.correspondence p).toEquiv

theorem patternCoarseningEquiv_eq_kernel {n : Nat} (p : ColorPattern n)
    (r : {r : ColorPattern n // p ≤ r}) :
    patternCoarseningEquiv p r = Setoid.ker (Quot.mapRight r.property) := by
  apply Setoid.ext
  intro x y
  induction x using Quotient.inductionOn with
  | h i =>
    induction y using Quotient.inductionOn with
    | h j =>
      change r.val i j ↔ Quotient.mk r.val i = Quotient.mk r.val j
      exact Quotient.eq.symm

/-- Passing to the quotient does not change the number of resulting colors. -/
theorem patternCoarseningEquiv_class_count {n : Nat} (p : ColorPattern n)
    (r : {r : ColorPattern n // p ≤ r}) :
    Nat.card (Quotient (patternCoarseningEquiv p r)) =
      colorPatternClassCount r.val := by
  rw [patternCoarseningEquiv_eq_kernel]
  exact Nat.card_congr (Setoid.quotientQuotientEquivQuotient p r.val r.property)

/-- The correspondence restricts to exactly k resulting color classes. -/
def patternCoarseningClassEquiv {n : Nat} (p : ColorPattern n) (k : Nat) :
    {r : {r : ColorPattern n // p ≤ r} // colorPatternClassCount r.val = k} ≃
      {s : Setoid (Quotient p) // Nat.card (Quotient s) = k} :=
  (patternCoarseningEquiv p).subtypeEquiv (fun r => by
    rw [patternCoarseningEquiv_class_count])

theorem patternCoarseningClass_card {n : Nat} (p : ColorPattern n) (k : Nat) :
    Nat.card {r : {r : ColorPattern n // p ≤ r} // colorPatternClassCount r.val = k} =
      Nat.card {s : Setoid (Quotient p) // Nat.card (Quotient s) = k} :=
  Nat.card_congr (patternCoarseningClassEquiv p k)

#print axioms patternCoarseningEquiv_class_count
#print axioms patternCoarseningClass_card
end LC004
