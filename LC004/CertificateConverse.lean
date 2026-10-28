import LC004.CertificateDeletion

namespace LC004

/-- Delete an explicitly identified interval block from a word's
certificate. Empty and positive residual lengths are both covered. -/
theorem certificate_after_interval {q : Nat} {w : List (Fin q)}
    (left right : List (Fin q)) (a : Fin q) (k : Nat)
    (heq : w = left ++ List.replicate k a ++ right)
    (cert : Noncrossing23Certificate w.get)
    (b : List (Fin w.length)) (hb : b ∈ cert.blocks)
    (hinterval : ∀ p, p ∈ b ↔
      left.length ≤ p.val ∧ p.val < left.length + k) :
    HasNoncrossing23Certificate (left ++ right) := by
  subst w
  by_cases hn : 0 < (left ++ right).length
  · have hlen : (left ++ List.replicate k a ++ right).length =
        (left ++ right).length + k := by simp; omega
    exact delete_interval_of_length hlen cert left.length hn (by simp)
      b hb hinterval (left ++ right).get
      (insertedWordColor_old left right a k)
  · have he : left ++ right = [] :=
      List.length_eq_zero_iff.mp (by omega)
    simpa only [he] using has_certificate_empty q

/-- The key induction invariant: a nonempty certified word has a
strictly shorter certified word reached by one auxiliary erasure. -/
theorem certificate_has_smaller_certificate {q : Nat} {w : List (Fin q)}
    (hw : w ≠ []) (h : HasNoncrossing23Certificate w) :
    ∃ v, SmallErase w v ∧ HasNoncrossing23Certificate v ∧
      v.length < w.length := by
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
  have hleft : (w.take gap).length = gap := by
    simp only [List.length_take]
    omega
  have hcert := certificate_after_interval (w.take gap) (w.drop (gap + k))
    a k hdecomp cert b hb (by simpa only [hleft] using hmem)
  exact ⟨_, hactual, hcert, smallErase_length_lt hactual⟩

/-- Every complete noncrossing monochromatic 2/3 partition can be
executed as a finite contextual pair/triple erasure history. -/
theorem certificate_to_erases_empty {q : Nat} {w : List (Fin q)}
    (h : HasNoncrossing23Certificate w) : Erases w [] := by
  suffices hall : ∀ n, ∀ u : List (Fin q), u.length = n →
      HasNoncrossing23Certificate u → Erases u [] from hall w.length w rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro u hlen hcert
      by_cases he : u = []
      · subst u
        exact Erases.refl []
      · obtain ⟨v, hstep, hv, hlt⟩ := certificate_has_smaller_certificate he hcert
        exact Erases.next hstep (ih v.length (by omega) v rfl hv)

theorem certificate_iff_erases_empty {q : Nat} (w : List (Fin q)) :
    HasNoncrossing23Certificate w ↔ Erases w [] :=
  ⟨certificate_to_erases_empty, erases_empty_to_certificate⟩

theorem insertion_history_iff_certificate {q : Nat} (w : List (Fin q)) :
    InsertionHistory w ↔ HasNoncrossing23Certificate w :=
  (insertion_history_iff_erases_empty w).trans (certificate_iff_erases_empty w).symm

#print axioms certificate_has_smaller_certificate
#print axioms certificate_to_erases_empty
#print axioms certificate_iff_erases_empty

end LC004
