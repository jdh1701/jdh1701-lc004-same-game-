import LC004.MatchingPatternMerge

namespace LC004
open scoped BigOperators

noncomputable def patternClassPositions {n : Nat} (p : ColorPattern n)
    (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (p i)

noncomputable def selectedPatternPositions {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => Quotient.mk p i ∈ chosen)

noncomputable def patternQuotientFiber {n : Nat} (p : ColorPattern n)
    (q : Quotient p) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => Quotient.mk p i = q)

theorem pair_pattern_quotient_fiber_card {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (q : Quotient p) :
    (patternQuotientFiber p q).card = 2 := by
  classical
  induction q using Quotient.inductionOn with
  | h i =>
    unfold patternQuotientFiber
    have hf : ((Finset.univ : Finset (Fin n)).filter
        (fun j => Quotient.mk p j = Quotient.mk p i)) =
        Finset.univ.filter (p i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => p.symm (Quotient.exact h),
        fun h => Quotient.sound (p.symm h)⟩
    rw [hf]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hp.1 i

theorem selected_pair_positions_card {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (chosen : Finset (Quotient p)) :
    (selectedPatternPositions p chosen).card = 2 * chosen.card := by
  classical
  have hsplit := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk p) (s := selectedPatternPositions p chosen) (t := chosen)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  calc
    _ = ∑ q ∈ chosen,
        ((selectedPatternPositions p chosen).filter (fun i => Quotient.mk p i = q)).card := hsplit
    _ = ∑ q ∈ chosen, 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hf : (selectedPatternPositions p chosen).filter
          (fun i => Quotient.mk p i = q) =
          Finset.univ.filter (fun i => Quotient.mk p i = q) := by
        ext i
        simp only [selectedPatternPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨by simpa only [h] using hq, h⟩
      rw [hf]
      exact pair_pattern_quotient_fiber_card p hp q
    _ = _ := by simp [Nat.mul_comm]

theorem merged_class_of_selected {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) (i : Fin n)
    (hi : Quotient.mk p i ∈ chosen) :
    patternClassPositions (mergePatternClasses p chosen) i =
      selectedPatternPositions p chosen := by
  classical
  ext j
  simp only [patternClassPositions, selectedPatternPositions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with hij | ⟨_, hj⟩
    · simpa only [Quotient.sound hij] using hi
    · exact hj
  · intro hj
    exact Or.inr ⟨hi, hj⟩

theorem merged_class_of_unselected {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) (i : Fin n)
    (hi : Quotient.mk p i ∉ chosen) :
    patternClassPositions (mergePatternClasses p chosen) i =
      patternClassPositions p i := by
  classical
  ext j
  simp only [patternClassPositions, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => (hi h.1).elim), Or.inl⟩

/-- The actual global merge has the intended fourfold-plus-pairs
multiplicities. This does not yet establish winning or surjectivity. -/
theorem fourfold_representation_class_card {n : Nat}
    (r : FourfoldMatchingRepresentation n) (i : Fin n) :
    (Quotient.mk r.1.val i ∈ r.2.val →
      (patternClassPositions (fourfoldRepresentationPattern r) i).card = 4) ∧
    (Quotient.mk r.1.val i ∉ r.2.val →
      (patternClassPositions (fourfoldRepresentationPattern r) i).card = 2) := by
  classical
  change (_ → (patternClassPositions (mergePatternClasses r.1.val r.2.val) i).card = 4) ∧
    (_ → (patternClassPositions (mergePatternClasses r.1.val r.2.val) i).card = 2)
  constructor <;> intro hi
  · rw [merged_class_of_selected _ _ _ hi,
      selected_pair_positions_card _ r.1.property, r.2.property]
  · rw [merged_class_of_unselected _ _ _ hi]
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using r.1.property.1 i

/-- There is one four-position class; every class of size four is
that same merged class. The original matching is still remembered here. -/
theorem fourfold_representation_unique_four_class {n : Nat}
    (r : FourfoldMatchingRepresentation n) :
    ∃ i : Fin n,
      (patternClassPositions (fourfoldRepresentationPattern r) i).card = 4 ∧
      ∀ j, fourfoldRepresentationPattern r i j ↔
        (patternClassPositions (fourfoldRepresentationPattern r) j).card = 4 := by
  classical
  have hpos : 0 < r.2.val.card := by rw [r.2.property]; decide
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  obtain ⟨i, rfl⟩ := Quotient.mk_surjective q
  refine ⟨i, (fourfold_representation_class_card r i).1 hq, ?_⟩
  intro j
  constructor
  · intro hij
    have hj : Quotient.mk r.1.val j ∈ r.2.val := by
      rcases hij with hij | ⟨_, hj⟩
      · simpa only [Quotient.sound hij] using hq
      · exact hj
    exact (fourfold_representation_class_card r j).1 hj
  · intro hj
    have hmem : Quotient.mk r.1.val j ∈ r.2.val := by
      by_contra hn
      have hc := (fourfold_representation_class_card r j).2 hn
      omega
    exact Or.inr ⟨hq, hmem⟩

/-- The selected classes are exactly those incident to a newly related
pair. Thus selection can be reconstructed from the original and merged
partitions, without naming either selected edge. -/
theorem selected_class_iff_new_relation {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) (hcard : 1 < chosen.card) (i : Fin n) :
    Quotient.mk p i ∈ chosen ↔
      ∃ j, mergePatternClasses p chosen i j ∧ ¬ p i j := by
  classical
  constructor
  · intro hi
    obtain ⟨q, hq, hne⟩ := Finset.exists_mem_ne hcard (Quotient.mk p i)
    obtain ⟨j, rfl⟩ := Quotient.mk_surjective q
    exact ⟨j, Or.inr ⟨hi, hq⟩, fun hij => hne (Quotient.sound hij).symm⟩
  · rintro ⟨j, hij, hnot⟩
    exact hij.elim (fun h => (hnot h).elim) (fun h => h.1)

theorem merge_selection_injective {n : Nat} (p : ColorPattern n)
    (s t : Finset (Quotient p)) (hs : 1 < s.card) (ht : 1 < t.card)
    (h : mergePatternClasses p s = mergePatternClasses p t) : s = t := by
  classical
  ext q
  induction q using Quotient.inductionOn with
  | h i =>
    rw [selected_class_iff_new_relation p s hs i,
      selected_class_iff_new_relation p t ht i, h]

#print axioms fourfold_representation_class_card
#print axioms merge_selection_injective
#print axioms fourfold_representation_unique_four_class

end LC004
