import LC004.InnermostBlock

namespace LC004

theorem smallErase_length_lt {q : Nat} {u v : List (Fin q)}
    (h : SmallErase u v) : v.length < u.length := by
  cases h <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

/-- A nonempty certificate identifies a legal first auxiliary erasure
in the actual word, with a strictly shorter result. This does not yet
assert that the shorter word inherits a complete certificate. -/
theorem certificate_has_first_erasure {q : Nat} {w : List (Fin q)}
    (hw : w ≠ []) (h : HasNoncrossing23Certificate w) :
    ∃ v, SmallErase w v ∧ v.length < w.length := by
  classical
  obtain ⟨cert⟩ := h
  obtain ⟨b, hb, gap, k, hk, hbound, hmem, a, hmono⟩ :=
    cert.exists_contiguous_monochromatic_block (List.ne_nil_iff_length_pos.mp hw)
  have hsegment : (w.drop gap).take k = List.replicate k a := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_replicate]
      omega
    · intro i hi hi'
      have hik : i < k := by simpa only [List.length_replicate] using hi'
      have hip : gap + i < w.length := by omega
      have hp : (⟨gap + i, hip⟩ : Fin w.length) ∈ b :=
        (hmem _).mpr (by
          change gap ≤ gap + i ∧ gap + i < gap + k
          omega)
      simpa only [List.getElem_take, List.getElem_drop, List.getElem_replicate,
        List.get_eq_getElem] using hmono ⟨gap + i, hip⟩ hp
  have hdecomp : w = w.take gap ++ List.replicate k a ++ w.drop (gap + k) := by
    calc
      w = w.take gap ++ w.drop gap := (List.take_append_drop gap w).symm
      _ = w.take gap ++ ((w.drop gap).take k ++ (w.drop gap).drop k) := by
        exact congrArg (fun rest => w.take gap ++ rest)
          (List.take_append_drop k (w.drop gap)).symm
      _ = _ := by simp only [hsegment, List.drop_drop, List.append_assoc]
  have hstep : SmallErase
      (w.take gap ++ List.replicate k a ++ w.drop (gap + k))
      (w.take gap ++ w.drop (gap + k)) := by
    rcases hk with rfl | rfl
    · simpa [List.replicate_succ] using
        SmallErase.pair (w.take gap) (w.drop (gap + 2)) a
    · simpa [List.replicate_succ] using
        SmallErase.triple (w.take gap) (w.drop (gap + 3)) a
  have hactual : SmallErase w (w.take gap ++ w.drop (gap + k)) :=
    Eq.mpr (congrArg
      (fun u => SmallErase u (w.take gap ++ w.drop (gap + k))) hdecomp) hstep
  exact ⟨_, hactual, smallErase_length_lt hactual⟩

#print axioms certificate_has_first_erasure

end LC004
