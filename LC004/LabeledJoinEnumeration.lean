import LC004.WinningConstraintGenerators

namespace LC004
open scoped BigOperators Classical

/-- Colorings satisfying an equality constraint are exactly functions on
its quotient. Colors on distinct quotient classes need not be distinct. -/
noncomputable def constraintColoringEquiv {n : Nat} (p : ColorPattern n) (b : Nat) :
    {f : Fin n → Fin b // p ≤ colorPatternOf f} ≃ (Quotient p → Fin b) where
  toFun f := Quotient.lift f.val (fun i j h => f.property h)
  invFun g := ⟨fun i => g (Quotient.mk p i), fun i j h => congrArg g (Quotient.sound h)⟩
  left_inv f := by rfl
  right_inv g := by
    funext x
    induction x using Quotient.inductionOn with
    | h i => rfl

theorem constraintColoring_card {n : Nat} (p : ColorPattern n) (b : Nat) :
    Nat.card {f : Fin n → Fin b // p ≤ colorPatternOf f} =
      b ^ colorPatternClassCount p := by
  rw [Nat.card_congr (constraintColoringEquiv p b), Nat.card_fun]
  simp [colorPatternClassCount, Nat.card_eq_fintype_card]

/-- The original maximal-run OEIS counting function, including n=0. -/
noncomputable def labeledWinningCount (b n : Nat) : Nat :=
  Nat.card {f : Fin n → Fin b // RawMaxErases (List.ofFn f) []}

theorem sum_labeled_constraint {n : Nat} (p : ColorPattern n) (b : Nat) :
    (∑ f : Fin n → Fin b, constraintIndicator p (colorPatternOf f)) =
      (b ^ colorPatternClassCount p : Nat) := by
  classical
  have h := constraintColoring_card p b
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simp only [constraintIndicator]
  norm_cast
  simpa using h

theorem sum_labeled_joinTermScore {n : Nat}
    (ts : List (ColorPattern n × Int)) (b : Nat) :
    (∑ f : Fin n → Fin b, joinTermScore ts (colorPatternOf f)) =
      (ts.map (fun t => t.2 * ((b ^ colorPatternClassCount t.1 : Nat) : Int))).sum := by
  classical
  induction ts with
  | nil => simp [joinTermScore]
  | cons t ts ih =>
    have h (f : Fin n → Fin b) :
        joinTermScore (t :: ts) (colorPatternOf f) =
          t.2 * constraintIndicator t.1 (colorPatternOf f) +
          joinTermScore ts (colorPatternOf f) := by simp [joinTermScore]
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_labeled_constraint, ih, List.map_cons, List.sum_cons]

/-- Universal exact labeled-word formula. The term list may be enormous:
this formalizes inclusion-exclusion, not a compact solution to enumeration. -/
theorem labeledWinningCount_signed_joins (b n : Nat) :
    (labeledWinningCount b n : Int) =
      ((certificateJoinTerms (certificateConstraints n)).map
        (fun t => t.2 * ((b ^ colorPatternClassCount t.1 : Nat) : Int))).sum := by
  classical
  rw [← sum_labeled_joinTermScore]
  simp only [winning_signed_join_indicator, winning_color_pattern_iff_raw_win]
  unfold labeledWinningCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

#print axioms constraintColoringEquiv
#print axioms constraintColoring_card
#print axioms labeledWinningCount_signed_joins
end LC004

