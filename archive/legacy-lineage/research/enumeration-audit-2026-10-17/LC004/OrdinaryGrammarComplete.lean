import LC004.RawGame
import LC004.GrammarInsertion

namespace LC004

/-- Every successful raw move removes a contiguous monochromatic block of
at least two cells. This is derived from the actual run-index implementation. -/
theorem ordinaryStepAtFuel_block {fuel : Nat} {w t : RawState} {i : Nat}
    (hs : ordinaryStepAtFuel fuel w i = some t) :
    ∃ a b c m, 2 ≤ m ∧ w = a ++ List.replicate m c ++ b ∧ t = a ++ b := by
  induction fuel generalizing w t i with
  | zero => simp [ordinaryStepAtFuel] at hs
  | succ fuel ih =>
      cases w with
      | nil => simp [ordinaryStepAtFuel] at hs
      | cons c cs =>
          let same := cs.takeWhile (fun d => d == c)
          let rest := cs.dropWhile (fun d => d == c)
          have he : same ++ rest = cs := List.takeWhile_append_dropWhile
          by_cases hi : i = 0
          · subst i
            change (if same.isEmpty then none else some rest) = some t at hs
            by_cases hb : same.isEmpty = true
            · simp [hb] at hs
            · have ht : rest = t := by simpa [hb] using hs
              have hlen : 1 ≤ same.length := by
                have hne : same ≠ [] := by simpa using hb
                have := List.length_pos_iff.mpr hne
                omega
              have hr : same = List.replicate same.length c := by
                apply List.eq_replicate_length.mpr
                intro d hd
                simpa only [beq_iff_eq] using List.mem_takeWhile_imp hd
              refine ⟨[], rest, c, same.length+1, by omega, ?_, ?_⟩
              · simp only [List.nil_append, List.replicate_succ, List.cons_append]
                rw [← hr, he]
              · simpa using ht.symm
          · simp only [ordinaryStepAtFuel, if_neg hi] at hs
            change (ordinaryStepAtFuel fuel rest (i-1)).map
                (fun tail => c :: same ++ tail) = some t at hs
            cases ht : ordinaryStepAtFuel fuel rest (i-1) with
            | none => simp [ht] at hs
            | some tail =>
                have hout : t = c :: same ++ tail := by simpa [ht] using hs.symm
                obtain ⟨a,b,d,m,hm,hw,htail⟩ := ih ht
                refine ⟨c :: same ++ a, b, d, m, hm, ?_, ?_⟩
                · calc
                    c :: cs = c :: (same ++ rest) := by rw [he]
                    _ = (c :: same ++ a) ++ List.replicate m d ++ b := by
                      rw [hw]
                      simp [List.append_assoc]
                · rw [hout, htail]
                  simp [List.append_assoc]

theorem ordinaryStepAt_grammar_backward {w t : RawState} {i : Nat}
    (hs : ordinaryStepAt w i = some t) (ht : ClickGrammar t) : ClickGrammar w := by
  obtain ⟨a,b,c,m,hm,hw,he⟩ := ordinaryStepAtFuel_block hs
  rw [he] at ht
  rw [hw]
  exact clickGrammar_insert ht (clickGrammar_replicate c m hm)

theorem ordinaryFollow_grammar_backward (moves : List Nat) {w t : RawState}
    (hs : ordinaryFollow ordinaryStepAt w moves = some t)
    (ht : ClickGrammar t) : ClickGrammar w := by
  induction moves generalizing w with
  | nil =>
      have he : w = t := by simpa [ordinaryFollow] using hs
      simpa [he] using ht
  | cons i moves ih =>
      cases hstep : ordinaryStepAt w i with
      | none => simp [ordinaryFollow, hstep] at hs
      | some v =>
          apply ordinaryStepAt_grammar_backward hstep
          apply ih
          simpa [ordinaryFollow, hstep] using hs

/-- One direction of the raw-game/grammar bridge, for all raw words.
The converse remains a separate obligation. -/
theorem ordinarySolvable_clickGrammar {w : RawState}
    (h : OrdinarySolvable ordinaryStepAt w) : ClickGrammar w := by
  obtain ⟨moves, hm⟩ := h
  exact ordinaryFollow_grammar_backward moves hm ClickGrammar.empty

theorem ordinarySolvable_firstBlock {w : RawState}
    (h : OrdinarySolvable ordinaryStepAt w) : FirstBlock w :=
  (clickGrammar_iff_firstBlock w).mp (ordinarySolvable_clickGrammar h)

#print axioms ordinaryStepAtFuel_block
#print axioms ordinarySolvable_clickGrammar
#print axioms ordinarySolvable_firstBlock

end LC004
