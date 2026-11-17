import LC004.SmallPatternCorrespondence
import LC004.FourfoldDoubleFiber

namespace LC004

theorem four_class_rel_iff {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hclass : patternClassPositions p a = {a, b, c, d}) (x : Fin n) :
    p a x ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  have hmem : x ∈ patternClassPositions p a ↔ x ∈ ({a, b, c, d} : Finset (Fin n)) := by rw [hclass]
  simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton] using hmem

/-- Split off the two indicated positions from their original class.
The relation uses only equality of tags, so it is an equivalence relation. -/
def splitPairClass {n : Nat} (p : ColorPattern n) (a b : Fin n) : ColorPattern n where
  r i j := p i j ∧ ((i = a ∨ i = b) ↔ (j = a ∨ j = b))
  iseqv := ⟨fun i => ⟨p.refl i, Iff.rfl⟩,
    fun h => ⟨p.symm h.1, h.2.symm⟩,
    fun h k => ⟨p.trans h.1 k.1, h.2.trans k.2⟩⟩

theorem splitPairClass_refines {n : Nat} (p : ColorPattern n) (a b : Fin n) :
    ∀ i j, splitPairClass p a b i j → p i j := fun _ _ h => h.1

theorem splitPairClass_cut_related {n : Nat} (p : ColorPattern n)
    {a b : Fin n} (hab : p a b) : splitPairClass p a b a b :=
  ⟨hab, ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl⟩⟩

theorem splitPairClass_cut_class {n : Nat} (p : ColorPattern n)
    {a b : Fin n} (hab : p a b) :
    patternClassPositions (splitPairClass p a b) a = {a, b} := by
  classical
  ext j
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  change (p a j ∧ ((a = a ∨ a = b) ↔ (j = a ∨ j = b))) ↔ j = a ∨ j = b
  constructor
  · exact fun h => h.2.mp (Or.inl rfl)
  · intro h
    have hpaj : p a j := by
      rcases h with h | h
      · subst j
        exact p.refl a
      · subst j
        exact hab
    exact ⟨hpaj, ⟨fun _ => h, fun _ => Or.inl rfl⟩⟩

theorem splitPairClass_outside_rel {n : Nat} (p : ColorPattern n)
    {a b i : Fin n} (hab : p a b) (hi : ¬ p a i) :
    ∀ j, splitPairClass p a b i j ↔ p i j := by
  have htagi : ¬ (i = a ∨ i = b) := by
    rintro (h | h)
    · subst i
      exact hi (p.refl a)
    · subst i
      exact hi hab
  intro j
  constructor
  · exact fun h => h.1
  · intro hij
    have htagj : ¬ (j = a ∨ j = b) := by
      rintro (h | h)
      · subst j
        exact hi (p.symm hij)
      · subst j
        exact hi (p.trans hab (p.symm hij))
    exact ⟨hij, ⟨fun h => (htagi h).elim, fun h => (htagj h).elim⟩⟩

theorem splitPairClass_complement_class {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hclass : patternClassPositions p a = {a, b, c, d})
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    patternClassPositions (splitPairClass p a b) c = {c, d} := by
  classical
  have hpac := (four_class_rel_iff p hclass c).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hpad := (four_class_rel_iff p hclass d).mpr (Or.inr (Or.inr (Or.inr rfl)))
  ext j
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  change (p c j ∧ ((c = a ∨ c = b) ↔ (j = a ∨ j = b))) ↔ j = c ∨ j = d
  constructor
  · intro h
    have hnot : ¬ (j = a ∨ j = b) := fun hj => (h.2.mpr hj).elim hca hcb
    have hcover := (four_class_rel_iff p hclass j).mp (p.trans hpac h.1)
    tauto
  · intro h
    have hpcj : p c j := by
      rcases h with h | h
      · subst j
        exact p.refl c
      · subst j
        exact p.trans (p.symm hpac) hpad
    have hnot : ¬ (j = a ∨ j = b) := by
      rcases h with h | h
      · subst j
        tauto
      · subst j
        tauto
    exact ⟨hpcj, ⟨fun h => h.elim (fun h => (hca h).elim) (fun h => (hcb h).elim),
      fun h => (hnot h).elim⟩⟩

/-- Splitting one four-position class into two pairs gives a perfect
matching as a position partition; noncrossing is proved separately. -/
theorem splitPairClass_classes_two {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    ∀ i, Nat.card {j : Fin n // splitPairClass p a b i j} = 2 := by
  classical
  have hpab := (four_class_rel_iff p hclass b).mpr (Or.inr (Or.inl rfl))
  have hcut := splitPairClass_cut_class p hpab
  have hcomp := splitPairClass_complement_class p hclass hca hcb hda hdb
  have hpcd : splitPairClass p a b c d := by
    have hmem : d ∈ patternClassPositions (splitPairClass p a b) c := by rw [hcomp]; simp
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have habclass := pattern_class_eq_of_related (splitPairClass p a b) (splitPairClass_cut_related p hpab)
  have hcdclass := pattern_class_eq_of_related (splitPairClass p a b) hpcd
  intro i
  have hcard : (patternClassPositions (splitPairClass p a b) i).card = 2 := by
    by_cases hi : p a i
    · rcases (four_class_rel_iff p hclass i).mp hi with h | h | h | h
      · subst i
        rw [hcut]
        simp [hab]
      · subst i
        rw [← habclass, hcut]
        simp [hab]
      · subst i
        rw [hcomp]
        simp [hcd]
      · subst i
        rw [← hcdclass, hcomp]
        simp [hcd]
    · have heq : patternClassPositions (splitPairClass p a b) i = patternClassPositions p i := by
        ext j
        simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        exact splitPairClass_outside_rel p hpab hi j
      rw [heq]
      exact hrest i hi
  simpa only [patternClassPositions, Nat.card_eq_fintype_card, Fintype.card_subtype] using hcard

/-- Splitting the first position with the second or the last gives
noncrossing matching pairs whenever the coarse partition is noncrossing. -/
theorem splitPairClass_no_alternation {n : Nat} (p : ColorPattern n)
    (hnc : PatternNoncrossing p) {a b c d e : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (he : e = b ∨ e = d) : PatternNoAlternation (splitPairClass p a e) := by
  intro i j k l hij hjk hkl hcross
  have hpij := hnc i j k l hij hjk hkl hcross.1.1 hcross.2.1
  have hpil := p.trans hpij hcross.2.1
  have hge := four_related_positions_card_ge_four p hij hjk hkl hpij hcross.1.1 hpil
  have hai : p a i := by
    by_contra hnot
    have htwo := hrest i hnot
    omega
  have haj := p.trans hai hpij
  have hak := p.trans hai hcross.1.1
  have hal := p.trans hai hpil
  have hi := (four_class_rel_iff p hclass i).mp hai
  have hj := (four_class_rel_iff p hclass j).mp haj
  have hk := (four_class_rel_iff p hclass k).mp hak
  have hl := (four_class_rel_iff p hclass l).mp hal
  have hieq : i = a := by omega
  have hkeq : k = c := by omega
  have htag : k = a ∨ k = e := hcross.1.2.mp (Or.inl hieq)
  rcases he with he | he <;> rcases htag with htag | htag <;> omega

#print axioms splitPairClass_classes_two
#print axioms splitPairClass_no_alternation

end LC004
