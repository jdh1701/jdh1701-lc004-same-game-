import LC004.SecondDiagonalArithmetic

namespace LC004

theorem one_class_pattern_eq_top {n : Nat} (p : ColorPattern n)
    (h : colorPatternClassCount p = 1) : p = ⊤ := by
  have hs : Subsingleton (Quotient p) := (Nat.card_eq_one_iff_unique.mp h).1
  apply Setoid.ext
  intro i j
  change p i j ↔ True
  exact iff_true_intro (Quotient.exact (hs.elim (Quotient.mk p i) (Quotient.mk p j)))

/-- The second-diagonal endpoint is an unconditional actual pattern count. -/
theorem second_diagonal_one_color_count : winningColorPatternCount 4 1 = 1 := by
  classical
  let color : Fin 4 → Fin 1 := fun _ => 0
  have htop : colorPatternOf color = (⊤ : ColorPattern 4) := by
    apply Setoid.ext
    intro i j
    change (0 : Fin 1) = 0 ↔ True
    simp
  have hc : colorPatternClassCount (⊤ : ColorPattern 4) = 1 := by
    rw [← htop, colorPatternClassCount_of]
    decide
  have hw : WinningColorPattern (⊤ : ColorPattern 4) := by
    rw [← htop, winning_color_pattern_iff_raw_win]
    have hr : RawMaxErases ([0, 0, 0, 0] : List (Fin 1)) [] :=
      RawMaxErases.next (RawMaxStep.delete [] [] 0 4 (by decide) (by decide) (by decide))
        (RawMaxErases.refl [])
    exact hr
  letI : Unique {p : ColorPattern 4 // WinningColorPattern p ∧ colorPatternClassCount p = 1} :=
    { default := ⟨⊤, hw, hc⟩
      uniq := fun p => Subtype.ext (one_class_pattern_eq_top p.val p.property.2) }
  exact Fintype.card_unique

theorem second_diagonal_formula_at_one :
    winningColorPatternCount (2 * 1 + 2) 1 =
      1 * (2 * 1 + 2).choose (1 - 1) := by
  simpa using second_diagonal_one_color_count

#print axioms second_diagonal_one_color_count
#print axioms second_diagonal_formula_at_one

end LC004
