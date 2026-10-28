import LC004.FourfoldRepresentationSurjection

namespace LC004

theorem pair_pattern_class_eq_pair {n : Nat} (m : ColorPattern n)
    (hm : NoncrossingPairPattern m) {a b : Fin n} (hne : a ≠ b) (hab : m a b) :
    patternClassPositions m a = {a, b} := by
  classical
  have hc : (patternClassPositions m a).card = 2 := by
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using hm.1 a
  have hpair : ({a, b} : Finset (Fin n)).card = 2 := by simp [hne]
  have hsub : ({a, b} : Finset (Fin n)) ⊆ patternClassPositions m a := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [patternClassPositions, m.refl]
    · have hxb := Finset.mem_singleton.mp hx
      subst x
      simp [patternClassPositions, hab]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, hpair])).symm

theorem pair_pattern_rel_iff {n : Nat} (m : ColorPattern n)
    (hm : NoncrossingPairPattern m) {a b : Fin n} (hne : a ≠ b) (hab : m a b)
    (x : Fin n) : m a x ↔ x = a ∨ x = b := by
  classical
  have hmem : x ∈ patternClassPositions m a ↔ x ∈ ({a, b} : Finset (Fin n)) := by
    rw [pair_pattern_class_eq_pair m hm hne hab]
  simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton] using hmem

theorem pair_pattern_has_other {n : Nat} (m : ColorPattern n)
    (hm : NoncrossingPairPattern m) (a : Fin n) :
    ∃ b, b ≠ a ∧ m a b := by
  classical
  have hc : (patternClassPositions m a).card = 2 := by
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using hm.1 a
  obtain ⟨b, hb, hne⟩ := Finset.exists_mem_ne (show 1 <
    (patternClassPositions m a).card by omega) a
  refine ⟨b, hne, ?_⟩
  simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hb

/-- Once one pair in a four-position color class is fixed, the other
pair is forced by the matching's size-two classes and refinement. -/
theorem four_refinement_complement {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    {a b c d : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hcover : ∀ x, p a x → x = a ∨ x = b ∨ x = c ∨ x = d)
    (hac : p a c) (hmatch : m a b) : m c d := by
  have hnca : ¬ m c a := by
    intro h
    rcases (pair_pattern_rel_iff m hm hab hmatch c).mp (m.symm h) with h | h
    · exact hca h
    · exact hcb h
  obtain ⟨x, hxc, hcx⟩ := pair_pattern_has_other m hm c
  rcases hcover x (p.trans hac (href c x hcx)) with h | h | h | h
  · subst x
    exact (hnca hcx).elim
  · subst x
    exact (hnca (m.trans hcx (m.symm hmatch))).elim
  · exact (hxc h).elim
  · exact h ▸ hcx

/-- A noncrossing matching refinement of four ordered positions has
exactly one of the two possible internal pairing shapes. -/
theorem four_refinement_two_shapes {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d}) :
    (m a b ∧ m c d) ∨ (m a d ∧ m b c) := by
  classical
  have hcover (x : Fin n) (hx : p a x) : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hmem : x ∈ patternClassPositions p a := by simp [patternClassPositions, hx]
    rw [hclass] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hpa (x : Fin n) (hx : x ∈ ({a, b, c, d} : Finset (Fin n))) : p a x := by
    have hmem : x ∈ patternClassPositions p a := hclass.symm ▸ hx
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  obtain ⟨x, hxa, hax⟩ := pair_pattern_has_other m hm a
  rcases hcover x (href a x hax) with h | h | h | h
  · exact (hxa h).elim
  · subst x
    left
    exact ⟨hax, four_refinement_complement m p hm href
      (by omega) (by omega) (by omega) hcover (hpa c (by simp)) hax⟩
  · subst x
    have hbd : m b d := four_refinement_complement m p hm href
      (by omega) (by omega) (by omega)
      (fun x hx => by have h := hcover x hx; tauto) (hpa b (by simp)) hax
    exact (hm.2 a b c d hab hbc hcd ⟨hax, hbd⟩).elim
  · subst x
    right
    exact ⟨hax, four_refinement_complement m p hm href
      (by omega) (by omega) (by omega)
      (fun x hx => by have h := hcover x hx; tauto) (hpa b (by simp)) hax⟩

/-- Two refinements agreeing on the two internal pairs agree globally:
all other color classes are forced pairs. -/
theorem matching_refinements_eq_of_pairs {n : Nat} (m t p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hmref : ∀ i j, m i j → p i j) (htref : ∀ i j, t i j → p i j)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (hmab : m a b) (hmcd : m c d) (htab : t a b) (htcd : t c d) : m = t := by
  classical
  apply Setoid.ext
  intro i j
  by_cases hi : p a i
  · have hmem : i ∈ ({a, b, c, d} : Finset (Fin n)) := by
      rw [← hclass]
      simp [patternClassPositions, hi]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · rw [pair_pattern_rel_iff m hm hab hmab, pair_pattern_rel_iff t ht hab htab]
    · rw [pair_pattern_rel_iff m hm hab.symm (m.symm hmab),
        pair_pattern_rel_iff t ht hab.symm (t.symm htab)]
    · rw [pair_pattern_rel_iff m hm hcd hmcd, pair_pattern_rel_iff t ht hcd htcd]
    · rw [pair_pattern_rel_iff m hm hcd.symm (m.symm hmcd),
        pair_pattern_rel_iff t ht hcd.symm (t.symm htcd)]
  · rw [matching_refinement_forced_pair m p hm hmref i (hrest i hi),
      matching_refinement_forced_pair t p ht htref i (hrest i hi)]

#print axioms four_refinement_two_shapes
#print axioms matching_refinements_eq_of_pairs

end LC004
