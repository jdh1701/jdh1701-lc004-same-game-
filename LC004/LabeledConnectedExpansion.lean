import LC004.LabeledJoinEnumeration
import LC004.WeightedConnectedFibers

namespace LC004
open scoped BigOperators Classical

theorem collectedJoinCoefficient_weighted_sum {n : Nat}
    (ts : List (ColorPattern n × Int)) (w : ColorPattern n → Int) :
    (∑ p : ColorPattern n, collectedJoinCoefficient ts p * w p) =
      (ts.map (fun t => t.2 * w t.1)).sum := by
  classical
  induction ts with
  | nil => simp [collectedJoinCoefficient]
  | cons t ts ih =>
    have he (p : ColorPattern n) : collectedJoinCoefficient (t :: ts) p =
        (if t.1 = p then t.2 else 0) + collectedJoinCoefficient ts p := by
      simp [collectedJoinCoefficient]
    simp_rw [he, add_mul]
    rw [Finset.sum_add_distrib, ih]
    simp

/-- The original maximal-run winning count equals the collected weighted sum. -/
theorem labeledWinningCount_collected (b n : Nat) :
    (labeledWinningCount b n : Int) = ∑ p : ColorPattern n,
      weightedGameCoefficient (b : Int) n p := by
  rw [labeledWinningCount_signed_joins]
  unfold weightedGameCoefficient winningJoinCoefficient
  rw [collectedJoinCoefficient_weighted_sum]
  simp [colorPatternClassCount]

/-- Noncrossing connected-weight expansion for the original game counts. -/
theorem labeledWinningCount_connected_expansion (b n : Nat) :
    (labeledWinningCount b n : Int) =
      ∑ pi : ColorPattern n, if PatternNoncrossing pi then
        (∏ q : Quotient pi, connectedGameWeight (b : Int) (patternQuotientFiber pi q).card) else 0 := by
  rw [labeledWinningCount_collected, weighted_game_noncrossing_expansion]

#print axioms labeledWinningCount_collected
#print axioms labeledWinningCount_connected_expansion
end LC004
