import LC004.FourfoldMatchingChoices
import LC004.DoubleRepresentationCount

namespace LC004

theorem ordered_fourfold_profile {n : Nat} (p : ColorPattern n)
    (hp : FourfoldPairPattern p) :
    ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧
      patternClassPositions p a = {a, b, c, d} ∧
      ∀ i, ¬ p a i → (patternClassPositions p i).card = 2 := by
  classical
  obtain ⟨e, he, hrest⟩ := hp
  let s := patternClassPositions p e
  let f : Fin 4 ↪o Fin n := s.orderEmbOfFin he
  have hset : s = {f 0, f 1, f 2, f 3} := by
    have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    have h := Finset.image_orderEmbOfFin_univ s he
    rw [huniv] at h
    apply Finset.ext
    intro x
    have hx := Iff.of_eq (congrArg (fun t : Finset (Fin n) => x ∈ t) h.symm)
    simpa only [Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton] using hx
  have hea : p e (f 0) := by
    have hmem := Finset.orderEmbOfFin_mem s he (0 : Fin 4)
    simpa only [s, patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmem
  refine ⟨f 0, f 1, f 2, f 3, f.strictMono (by decide),
    f.strictMono (by decide), f.strictMono (by decide), ?_, ?_⟩
  · exact (pattern_class_eq_of_related p hea).symm.trans hset
  · intro i hi
    apply hrest i
    intro hei
    exact hi (p.trans (p.symm hea) hei)

theorem matching_refinements_eq_of_first_pair {n : Nat} (m t p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hmref : ∀ i j, m i j → p i j) (htref : ∀ i j, t i j → p i j)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (hfirst : m a b ↔ t a b) : m = t := by
  classical
  have hmsh := four_refinement_two_shapes m p hm hmref hab hbc hcd hclass
  have htsh := four_refinement_two_shapes t p ht htref hab hbc hcd hclass
  rcases hmsh with hms | hmn
  · rcases htsh with hts | htn
    · exact matching_refinements_eq_of_pairs m t p hm ht hmref htref
        (by omega) (by omega) hclass hrest hms.1 hms.2 hts.1 hts.2
    · have htab := hfirst.mp hms.1
      have hbad := (pair_pattern_rel_iff t ht (show a ≠ d by omega) htn.1 b).mp htab
      rcases hbad with h | h <;> omega
  · rcases htsh with hts | htn
    · have hmab := hfirst.mpr hts.1
      have hbad := (pair_pattern_rel_iff m hm (show a ≠ d by omega) hmn.1 b).mp hmab
      rcases hbad with h | h <;> omega
    · have hclass' : patternClassPositions p a = {a, d, b, c} := by
        rw [hclass]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact matching_refinements_eq_of_pairs m t p hm ht hmref htref
        (by omega) (by omega) hclass' hrest hmn.1 hmn.2 htn.1 htn.2

theorem fourfold_representation_refines {n : Nat}
    (r : FourfoldMatchingRepresentation n) (p : ColorPattern n)
    (hr : fourfoldRepresentationPattern r = p) :
    ∀ i j, r.1.val i j → p i j := by
  intro i j hij
  rw [← hr]
  exact mergePatternClasses_coarsens r.1.val r.2.val hij

/-- For a fixed matching, equal merged outputs force equal unordered
selections. This removes all multiplicity from the choice data. -/
theorem fourfold_representations_eq_of_matching {n : Nat}
    (r s : FourfoldMatchingRepresentation n)
    (hm : r.1.val = s.1.val)
    (hp : fourfoldRepresentationPattern r = fourfoldRepresentationPattern s) : r = s := by
  classical
  rcases r with ⟨⟨m, hmprop⟩, ⟨cs, hcs⟩⟩
  rcases s with ⟨⟨t, htprop⟩, ⟨ct, hct⟩⟩
  change m = t at hm
  subst t
  have hsets : cs = ct := merge_selection_injective m cs ct
    (by omega) (by omega) hp
  subst ct
  rfl

noncomputable def fourfoldRepresentationFiber {n : Nat} (p : ColorPattern n) :
    Finset (FourfoldMatchingRepresentation n) := by
  classical
  exact Finset.univ.filter (fun r => fourfoldRepresentationPattern r = p)

/-- The actual global matching-to-pattern map has at most two
representations over any fourfold-plus-pairs pattern. -/
theorem fourfold_representation_fiber_le_two {n : Nat} (p : ColorPattern n)
    (hprofile : FourfoldPairPattern p) :
    (fourfoldRepresentationFiber p).card ≤ 2 := by
  classical
  obtain ⟨a, b, c, d, hab, hbc, hcd, hclass, hrest⟩ := ordered_fourfold_profile p hprofile
  let tag : FourfoldMatchingRepresentation n → Bool := fun r => decide (r.1.val a b)
  have hinj : Set.InjOn tag (fourfoldRepresentationFiber p) := by
    intro r hr s hs heq
    have hrp : fourfoldRepresentationPattern r = p := (Finset.mem_filter.mp hr).2
    have hsp : fourfoldRepresentationPattern s = p := (Finset.mem_filter.mp hs).2
    have hfirst : r.1.val a b ↔ s.1.val a b := by
      by_cases h1 : r.1.val a b
      · have h2 : s.1.val a b := by
          by_contra h2
          simp [tag, h1, h2] at heq
        exact ⟨fun _ => h2, fun _ => h1⟩
      · have h2 : ¬ s.1.val a b := by
          intro h2
          simp [tag, h1, h2] at heq
        exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    have hm : r.1.val = s.1.val := matching_refinements_eq_of_first_pair
      r.1.val s.1.val p r.1.property s.1.property
      (fourfold_representation_refines r p hrp) (fourfold_representation_refines s p hsp)
      hab hbc hcd hclass hrest hfirst
    exact fourfold_representations_eq_of_matching r s hm (hrp.trans hsp.symm)
  have hc := Finset.card_le_card_of_injOn tag
    (s := fourfoldRepresentationFiber p) (t := (Finset.univ : Finset Bool))
    (fun _ _ => Finset.mem_univ _) hinj
  simpa using hc

theorem fourfold_representation_fiber_one_or_two {n : Nat} (p : ColorPattern n)
    (hprofile : FourfoldPairPattern p) (hwin : WinningColorPattern p) :
    (fourfoldRepresentationFiber p).card = 1 ∨
      (fourfoldRepresentationFiber p).card = 2 := by
  classical
  obtain ⟨r, hr⟩ := fourfold_winning_has_representation p hprofile hwin
  have hpos : 0 < (fourfoldRepresentationFiber p).card :=
    Finset.card_pos.mpr ⟨r, by simp [fourfoldRepresentationFiber, hr]⟩
  have hbound := fourfold_representation_fiber_le_two p hprofile
  omega

open scoped Classical in
theorem fourfoldProfileMap_fiber {n : Nat}
    (p : {p : ColorPattern n // WinningColorPattern p ∧ FourfoldPairPattern p}) :
    ((Finset.univ : Finset (FourfoldMatchingRepresentation n)).filter
      (fun r => fourfoldRepresentationProfileMap r = p)) = fourfoldRepresentationFiber p.val := by
  classical
  ext r
  simp only [fourfoldRepresentationFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

noncomputable def fourfoldWinningPatternCount (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n // WinningColorPattern p ∧ FourfoldPairPattern p}

noncomputable def fourfoldDoublePatternCount (n : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset {p : ColorPattern n //
    WinningColorPattern p ∧ FourfoldPairPattern p}).filter
      (fun p => (fourfoldRepresentationFiber p.val).card = 2)).card

/-- Double-count subtraction is now instantiated with the actual
finite Same Game matching and winning-pattern spaces. The remaining
geometric task is to enumerate the doubly represented patterns. -/
theorem fourfold_winning_count_subtraction (n : Nat) :
    fourfoldWinningPatternCount n = fourfoldMatchingRepresentationCount n -
      fourfoldDoublePatternCount n := by
  classical
  have hbound (p : {p : ColorPattern n // WinningColorPattern p ∧ FourfoldPairPattern p}) :
      ((Finset.univ : Finset (FourfoldMatchingRepresentation n)).filter
        (fun r => fourfoldRepresentationProfileMap r = p)).card ≤ 2 := by
    rw [fourfoldProfileMap_fiber]
    exact fourfold_representation_fiber_le_two p.val p.property.2
  have h := finite_one_or_two_fiber_subtraction (@fourfoldRepresentationProfileMap n)
    (fourfoldRepresentationProfileMap_surjective n) hbound
  simpa only [fourfoldWinningPatternCount, fourfoldMatchingRepresentationCount,
    fourfoldDoublePatternCount, fourfoldProfileMap_fiber] using h

#print axioms fourfold_representation_fiber_le_two
#print axioms fourfold_representation_fiber_one_or_two
#print axioms fourfold_winning_count_subtraction

end LC004
