import LC004.RegionalClassCount
import LC004.NoncrossingConnectedFiber
import LC004.NoncrossingCoefficientPushforward

namespace LC004
open scoped BigOperators Classical

noncomputable def weightedGameCoefficient (b : Int) (n : Nat) (p : ColorPattern n) : Int :=
  winningJoinCoefficient n p * b ^ Nat.card (Quotient p)

noncomputable def connectedGameWeight (b : Int) (n : Nat) : Int :=
  ∑ p : {p : ColorPattern n // NCConnected p}, weightedGameCoefficient b n p.val

/-- Sum over the exact closure fiber factors into connected regional sums. -/
theorem weighted_connected_fiber_product {n : Nat} (b : Int) (pi : ColorPattern n)
    (hnc : PatternNoncrossing pi) :
    (∑ p : {p : ColorPattern n // noncrossingClosure p = pi},
      weightedGameCoefficient b n p.val) =
      ∏ q : Quotient pi, connectedGameWeight b (patternQuotientFiber pi q).card := by
  classical
  unfold connectedGameWeight
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (connectedClosureFiberEquiv pi hnc)
  intro p
  exact weighted_winningJoinCoefficient_regions p.val pi
    (by simpa only [p.property] using le_noncrossingClosure p.val) hnc b

theorem closurePushforward_eq_fiber_sum {n : Nat} (f : ColorPattern n → Int)
    (pi : ColorPattern n) :
    closurePushforward f pi = ∑ p : {p : ColorPattern n // noncrossingClosure p = pi}, f p.val := by
  classical
  unfold closurePushforward
  apply Finset.sum_congr_set {p : ColorPattern n | noncrossingClosure p = pi}
    (fun p => if noncrossingClosure p = pi then f p else 0) (fun p => f p.val)
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp [hp]
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp [hp]

theorem weighted_closurePushforward_product {n : Nat} (b : Int) (pi : ColorPattern n)
    (hnc : PatternNoncrossing pi) :
    closurePushforward (weightedGameCoefficient b n) pi =
      ∏ q : Quotient pi, connectedGameWeight b (patternQuotientFiber pi q).card := by
  rw [closurePushforward_eq_fiber_sum, weighted_connected_fiber_product b pi hnc]

/-- Exact noncrossing moment expansion for the collected signed game sum.
The identification with labeledWinningCount is a separate obligation. -/
theorem weighted_game_noncrossing_expansion (b : Int) (n : Nat) :
    (∑ p : ColorPattern n, weightedGameCoefficient b n p) =
      ∑ pi : ColorPattern n, if PatternNoncrossing pi then
        (∏ q : Quotient pi, connectedGameWeight b (patternQuotientFiber pi q).card) else 0 := by
  rw [← closurePushforward_total]
  apply Finset.sum_congr rfl
  intro pi _
  by_cases h : PatternNoncrossing pi
  · rw [if_pos h, weighted_closurePushforward_product b pi h]
  · rw [if_neg h, closurePushforward_zero_of_crossing _ pi h]

#print axioms weighted_connected_fiber_product
#print axioms weighted_game_noncrossing_expansion
end LC004
