import LC004.CertificatePairRefinement

namespace LC004

/-- Select matching classes lying in a specified original color class.
Refinement will ensure that membership is independent of representatives. -/
noncomputable def matchingClassesInside {n : Nat} (m p : ColorPattern n)
    (a : Fin n) : Finset (Quotient m) := by
  classical
  exact Finset.univ.filter (fun q => p a q.out)

theorem mem_matchingClassesInside {n : Nat} (m p : ColorPattern n)
    (href : ∀ i j, m i j → p i j) (a j : Fin n) :
    Quotient.mk m j ∈ matchingClassesInside m p a ↔ p a j := by
  classical
  simp only [matchingClassesInside, Finset.mem_filter, Finset.mem_univ, true_and]
  have hout : m (Quotient.mk m j).out j := Quotient.mk_out j
  have hpout := href _ _ hout
  exact ⟨fun h => p.trans h hpout, fun h => p.trans h (p.symm hpout)⟩

theorem matching_inside_positions {n : Nat} (m p : ColorPattern n)
    (href : ∀ i j, m i j → p i j) (a : Fin n) :
    selectedPatternPositions m (matchingClassesInside m p a) =
      patternClassPositions p a := by
  classical
  ext j
  simp only [selectedPatternPositions, patternClassPositions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_matchingClassesInside m p href a j

theorem four_class_contains_two_matching_classes {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    (a : Fin n) (ha : (patternClassPositions p a).card = 4) :
    (matchingClassesInside m p a).card = 2 := by
  classical
  have hcard := selected_pair_positions_card m hm (matchingClassesInside m p a)
  rw [matching_inside_positions m p href a, ha] at hcard
  omega

/-- On any original pair class, a matching refinement is forced to be
that same pair. Only the four-position class can be split differently. -/
theorem matching_refinement_forced_pair {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    (i : Fin n) (hi : (patternClassPositions p i).card = 2) :
    ∀ j, m i j ↔ p i j := by
  classical
  have hsub : patternClassPositions m i ⊆ patternClassPositions p i := by
    intro j hj
    have hmij : m i j := by
      simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using hj
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using href i j hmij
  have hmi : (patternClassPositions m i).card = 2 := by
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using hm.1 i
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hi, hmi])
  intro j
  have hmem : j ∈ patternClassPositions m i ↔ j ∈ patternClassPositions p i := by rw [heq]
  simpa only [patternClassPositions, Finset.mem_filter,
    Finset.mem_univ, true_and] using hmem

/-- Merging the matching classes inside the fourfold color recovers
all and only the equalities of the original pattern. -/
theorem merge_matching_classes_recovers {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    (a : Fin n)
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2) :
    mergePatternClasses m (matchingClassesInside m p a) = p := by
  classical
  apply Setoid.ext
  intro i j
  change (m i j ∨ (Quotient.mk m i ∈ matchingClassesInside m p a ∧
    Quotient.mk m j ∈ matchingClassesInside m p a)) ↔ p i j
  rw [mem_matchingClassesInside m p href a i, mem_matchingClassesInside m p href a j]
  constructor
  · rintro (h | ⟨hi, hj⟩)
    · exact href i j h
    · exact p.trans (p.symm hi) hj
  · intro hij
    by_cases hi : p a i
    · exact Or.inr ⟨hi, p.trans hi hij⟩
    · exact Or.inl ((matching_refinement_forced_pair m p hm href i (hrest i hi) j).mpr hij)

/-- Every winning fourfold-plus-pairs pattern has a genuine global
matching representation. This establishes surjectivity, not yet the
one-or-two fiber classification or a closed cardinality formula. -/
theorem fourfold_winning_has_representation {n : Nat} (p : ColorPattern n)
    (hprofile : FourfoldPairPattern p) (hwin : WinningColorPattern p) :
    ∃ r : FourfoldMatchingRepresentation n, fourfoldRepresentationPattern r = p := by
  classical
  obtain ⟨m, hm, href⟩ := fourfold_winning_has_pair_refinement p hprofile hwin
  obtain ⟨a, ha, hrest⟩ := hprofile
  let chosen := matchingClassesInside m p a
  have hchosen : chosen.card = 2 := four_class_contains_two_matching_classes m p hm href a ha
  refine ⟨⟨⟨m, hm⟩, ⟨chosen, hchosen⟩⟩, ?_⟩
  exact merge_matching_classes_recovers m p hm href a hrest

theorem fourfoldRepresentationProfileMap_surjective (n : Nat) :
    Function.Surjective (@fourfoldRepresentationProfileMap n) := by
  intro p
  obtain ⟨r, hr⟩ := fourfold_winning_has_representation p.val p.property.2 p.property.1
  exact ⟨r, Subtype.ext hr⟩

#print axioms fourfold_winning_has_representation
#print axioms fourfoldRepresentationProfileMap_surjective

end LC004
