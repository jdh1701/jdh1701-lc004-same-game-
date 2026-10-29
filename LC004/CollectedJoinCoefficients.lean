import LC004.FiniteIncidenceSupport
import LC004.WinningConstraintGenerators

namespace LC004
open scoped BigOperators Classical

/-- Collect equal partition constraints in a signed list. -/
noncomputable def collectedJoinCoefficient {n : Nat}
    (ts : List (ColorPattern n × Int)) (p : ColorPattern n) : Int := by
  classical
  exact (ts.map (fun t => if t.1 = p then t.2 else 0)).sum

theorem collectedJoinCoefficient_incidence {n : Nat}
    (ts : List (ColorPattern n × Int)) (r : ColorPattern n) :
    lowerIncidence (collectedJoinCoefficient ts) r = joinTermScore ts r := by
  classical
  induction ts with
  | nil => simp [collectedJoinCoefficient, lowerIncidence, joinTermScore]
  | cons t ts ih =>
    have hsingle : (∑ q : ColorPattern n,
        if q ≤ r then (if t.1 = q then t.2 else 0) else 0) =
        t.2 * constraintIndicator t.1 r := by
      rw [Finset.sum_eq_single t.1]
      · by_cases h : t.1 ≤ r <;> simp [constraintIndicator,h]
      · intro q _ hq
        simp [Ne.symm hq]
      · simp
    change (∑ q, if q ≤ r then
      (if t.1 = q then t.2 else 0) + collectedJoinCoefficient ts q else 0) = _
    simp_rw [ite_add_zero]
    rw [Finset.sum_add_distrib, hsingle]
    change _ + lowerIncidence (collectedJoinCoefficient ts) r = _
    rw [ih]
    simp [joinTermScore]

noncomputable def winningJoinCoefficient (n : Nat) : ColorPattern n → Int :=
  collectedJoinCoefficient (certificateJoinTerms (certificateConstraints n))

theorem winningJoinCoefficient_incidence {n : Nat} (r : ColorPattern n) :
    lowerIncidence (winningJoinCoefficient n) r =
      if WinningColorPattern r then 1 else 0 := by
  rw [winningJoinCoefficient, collectedJoinCoefficient_incidence,
    winning_signed_join_indicator]

/-- The collected signed coefficients are intrinsically determined by the
original game's winning indicator, independent of certificate-list ordering. -/
theorem winningJoinCoefficient_unique {n : Nat} (f : ColorPattern n → Int)
    (h : ∀ r, lowerIncidence f r = if WinningColorPattern r then 1 else 0) :
    f = winningJoinCoefficient n := by
  apply lowerIncidence_injective
  funext r
  rw [h, winningJoinCoefficient_incidence]

#print axioms collectedJoinCoefficient_incidence
#print axioms winningJoinCoefficient_incidence
#print axioms winningJoinCoefficient_unique
end LC004
