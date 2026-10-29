import LC004.NoncrossingClosure
import LC004.CollectedJoinCoefficients

namespace LC004
open scoped BigOperators Classical

/-- Sum signed weights over an exact noncrossing-closure fiber. -/
noncomputable def closurePushforward {n : Nat} (f : ColorPattern n → Int)
    (q : ColorPattern n) : Int :=
  ∑ p : ColorPattern n, if noncrossingClosure p = q then f p else 0

theorem closurePushforward_zero_of_crossing {n : Nat} (f : ColorPattern n → Int)
    (q : ColorPattern n) (hnc : ¬ PatternNoncrossing q) :
    closurePushforward f q = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  have he : noncrossingClosure p ≠ q := by
    intro h
    apply hnc
    rw [← h]
    exact noncrossingClosure_noncrossing p
  simp [he]

/-- Exact regrouping for arbitrary signed weights. No block-factorization
assumption is needed. This isolates the algebra from the game's next obligation. -/
theorem closurePushforward_incidence {n : Nat} (f : ColorPattern n → Int)
    (r : ColorPattern n) (hnc : PatternNoncrossing r) :
    lowerIncidence (closurePushforward f) r = lowerIncidence f r := by
  classical
  unfold lowerIncidence closurePushforward
  have expand (q : ColorPattern n) :
      (if q ≤ r then ∑ p, if noncrossingClosure p = q then f p else 0 else 0) =
      ∑ p : ColorPattern n, if q ≤ r then
        (if noncrossingClosure p = q then f p else 0) else 0 := by
    by_cases h : q ≤ r <;> simp [h]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (noncrossingClosure p)]
  · simp [noncrossingClosure_le_iff p r hnc]
  · intro q _ hq
    simp [Ne.symm hq]
  · simp

theorem closurePushforward_total {n : Nat} (f : ColorPattern n → Int) :
    (∑ q : ColorPattern n, closurePushforward f q) = ∑ p : ColorPattern n, f p := by
  classical
  have hnc : PatternNoncrossing (⊤ : ColorPattern n) := by
    intro a b c d _ _ _ _ _
    trivial
  have h := closurePushforward_incidence f ⊤ hnc
  simpa [lowerIncidence] using h

theorem closurePushforward_top {n : Nat} (f : ColorPattern n → Int) :
    closurePushforward f ⊤ =
      ∑ p : ColorPattern n, if NCConnected p then f p else 0 := rfl

/-- Original-game indicator recovered on every noncrossing coarsening after
collecting the already verified signed coefficients by NC closure. -/
theorem winning_closurePushforward_indicator {n : Nat} (r : ColorPattern n)
    (hnc : PatternNoncrossing r) :
    lowerIncidence (closurePushforward (winningJoinCoefficient n)) r =
      if WinningColorPattern r then 1 else 0 := by
  rw [closurePushforward_incidence _ r hnc,winningJoinCoefficient_incidence]

#print axioms closurePushforward_incidence
#print axioms closurePushforward_total
#print axioms winning_closurePushforward_indicator
end LC004
