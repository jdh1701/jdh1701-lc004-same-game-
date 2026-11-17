import LC004.WinningConstraintGenerators
import LC004.PatternCoarseningCorrespondence

namespace LC004
open scoped BigOperators Classical

/-- Number of k-class patterns satisfying a given equality constraint. -/
noncomputable def constraintCoarseningCount {n : Nat} (p : ColorPattern n) (k : Nat) : Nat := by
  classical
  exact (Finset.univ.filter (fun r : ColorPattern n =>
    colorPatternClassCount r = k ∧ p ≤ r)).card

theorem sum_constraintIndicator {n : Nat} (p : ColorPattern n) (k : Nat) :
    (∑ r ∈ Finset.univ.filter (fun r : ColorPattern n => colorPatternClassCount r = k),
      constraintIndicator p r) = (constraintCoarseningCount p k : Int) := by
  classical
  simp [constraintIndicator, constraintCoarseningCount, Finset.filter_filter]

/-- Finite summation exchanges the pattern sum and the signed term list. -/
theorem sum_joinTermScore {n : Nat} (ts : List (ColorPattern n × Int)) (k : Nat) :
    (∑ r ∈ Finset.univ.filter (fun r : ColorPattern n => colorPatternClassCount r = k),
      joinTermScore ts r) =
      (ts.map (fun t => t.2 * (constraintCoarseningCount t.1 k : Int))).sum := by
  classical
  induction ts with
  | nil => simp [joinTermScore]
  | cons t ts ih =>
    have h (r : ColorPattern n) : joinTermScore (t :: ts) r =
        t.2 * constraintIndicator t.1 r + joinTermScore ts r := by
      simp [joinTermScore]
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_constraintIndicator,
      ih, List.map_cons, List.sum_cons]

/-- Exact general enumeration by signed joins of certificate constraints.
This is a finite formula; no efficiency or compact closed-form claim is made. -/
theorem winningColorPatternCount_signed_joins (n k : Nat) :
    (winningColorPatternCount n k : Int) =
      ((certificateJoinTerms (certificateConstraints n)).map
        (fun t => t.2 * (constraintCoarseningCount t.1 k : Int))).sum := by
  classical
  rw [← sum_joinTermScore]
  simp only [winning_signed_join_indicator]
  simp [winningColorPatternCount, Fintype.card_subtype, Finset.filter_filter, and_comm]

#print axioms sum_joinTermScore
#print axioms winningColorPatternCount_signed_joins
end LC004
