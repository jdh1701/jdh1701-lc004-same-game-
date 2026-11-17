import LC004.RawRunInflation
import LC004.CertificateConverse
import LC004.ConditionalGrammarBridge

namespace LC004

theorem raw_inflates_context_cell {q : Nat}
    (left right : List (Fin q)) (a : Fin q) (extra : Nat) :
    RawInflates (left ++ a :: right)
      (left ++ List.replicate (extra + 1) a ++ right) := by
  simpa only [List.append_assoc] using
    raw_inflates_append (raw_inflates_refl left)
      (RawInflates.cons a extra (raw_inflates_refl right))

/-- Inserting a monochromatic block of length at least two anywhere
preserves genuine maximal-run solvability. If it touches its color it
inflates an existing run; otherwise it is a maximal run removable now. -/
theorem monochromatic_insertion_preserves_raw_win {q : Nat}
    (left right : List (Fin q)) (a : Fin q) (k : Nat) (hk : 2 ≤ k)
    (hwin : RawMaxErases (left ++ right) []) :
    RawMaxErases (left ++ List.replicate k a ++ right) [] := by
  by_cases hl : left.getLast? = some a
  · have hi : RawInflates (left ++ right)
        (left ++ List.replicate k a ++ right) := by
      obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hl
      simpa [List.append_assoc, List.replicate_succ] using
        raw_inflates_context_cell pre right a k
    exact raw_win_inflation hwin hi
  · by_cases hr : right.head? = some a
    · have hi : RawInflates (left ++ right)
          (left ++ List.replicate k a ++ right) := by
        obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hr
        have heq : List.replicate (k + 1) a ++ tail =
            List.replicate k a ++ a :: tail := by
          rw [List.replicate_add]
          simp
        simpa only [List.append_assoc, heq] using
          raw_inflates_context_cell left tail a k
      exact raw_win_inflation hwin hi
    · exact isolated_block_preserves_raw_win left right a k hk hl hr hwin

theorem auxiliary_step_lifts_raw_win {q : Nat} {u v : List (Fin q)}
    (hstep : SmallErase u v) (hwin : RawMaxErases v []) :
    RawMaxErases u [] := by
  cases hstep with
  | pair left right a =>
      simpa [List.replicate_succ] using
        monochromatic_insertion_preserves_raw_win left right a 2 (by omega) hwin
  | triple left right a =>
      simpa [List.replicate_succ] using
        monochromatic_insertion_preserves_raw_win left right a 3 (by omega) hwin

/-- The previously open semantic bridge, now proved for real maximal
run deletion with both boundary inequalities in RawMaxStep. -/
theorem aux_erases_to_raw_max_win {q : Nat} {w : List (Fin q)}
    (h : Erases w []) : RawMaxErases w [] := by
  exact erases_imply_win_of_one_step_lift
    (fun u => RawMaxErases u []) (RawMaxErases.refl [])
    (fun step win => auxiliary_step_lifts_raw_win step win) h

theorem raw_max_win_iff_aux_erases {q : Nat} (w : List (Fin q)) :
    RawMaxErases w [] ↔ Erases w [] :=
  ⟨raw_max_win_to_aux_erases, aux_erases_to_raw_max_win⟩

/-- Full structural characterization for any finite alphabet:
genuine maximal-run winning iff a complete noncrossing monochromatic
partition of original positions into blocks of size two or three. -/
theorem raw_max_win_iff_certificate {q : Nat} (w : List (Fin q)) :
    RawMaxErases w [] ↔ HasNoncrossing23Certificate w :=
  (raw_max_win_iff_aux_erases w).trans (certificate_iff_erases_empty w).symm

theorem raw_max_win_iff_insertion_history {q : Nat} (w : List (Fin q)) :
    RawMaxErases w [] ↔ InsertionHistory w :=
  (raw_max_win_iff_aux_erases w).trans (insertion_history_iff_erases_empty w).symm

/-- The pair/triple grammar is unconditionally sound for the genuine
maximal-run game; it no longer requires an unproved lifting hypothesis. -/
theorem grammar_to_raw_max_win {q : Nat} {w : List (Fin q)}
    (h : Grammar q w) : RawMaxErases w [] :=
  aux_erases_to_raw_max_win (grammar_erases_empty h)

#print axioms raw_win_inflation
#print axioms monochromatic_insertion_preserves_raw_win
#print axioms aux_erases_to_raw_max_win
#print axioms raw_max_win_iff_certificate
#print axioms grammar_to_raw_max_win

end LC004
