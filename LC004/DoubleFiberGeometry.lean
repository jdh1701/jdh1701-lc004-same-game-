import LC004.FourfoldSplit
import LC004.FourBlockOverlapCorollary

namespace LC004

theorem matching_related_pairs_no_cross {n : Nat} (m : ColorPattern n)
    (hm : NoncrossingPairPattern m) {u v x y : Fin n}
    (huv : m u v) (hxy : m x y) : ¬ PairCross u.val v.val x.val y.val := by
  intro hc
  rcases hc with ⟨hux, hxv, hvy⟩ | ⟨hxu, huy, hyv⟩
  · exact hm.2 u x v y hux hxv hvy ⟨huv, hxy⟩
  · exact hm.2 x u y v hxu huy hyv ⟨hxy, huv⟩

/-- Both global internal shapes force every external pair to avoid
crossing the coarse four-position block. -/
theorem both_shapes_external_pair_no_cross {n : Nat} (m t p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hmref : ∀ i j, m i j → p i j) (htref : ∀ i j, t i j → p i j)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (hmab : m a b) (hmcd : m c d) (htad : t a d) (htbc : t b c)
    {u v : Fin n} (huv : u < v) (hpuv : p u v) (huout : ¬ p a u) :
    ¬ FourBlockCross u.val v.val a.val b.val c.val d.val := by
  have hvout : ¬ p a v := fun h => huout (p.trans h (p.symm hpuv))
  have hun : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by
    have h := fun h => huout ((four_class_rel_iff p hclass u).mpr h)
    tauto
  have hvn : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
    have h := fun h => hvout ((four_class_rel_iff p hclass v).mpr h)
    tauto
  have huval : u.val ≠ a.val ∧ u.val ≠ b.val ∧ u.val ≠ c.val ∧ u.val ≠ d.val := by omega
  have hvval : v.val ≠ a.val ∧ v.val ≠ b.val ∧ v.val ≠ c.val ∧ v.val ≠ d.val := by omega
  have hmuv := (matching_refinement_forced_pair m p hm hmref u (hrest u huout) v).mpr hpuv
  have htuv := (matching_refinement_forced_pair t p ht htref u (hrest u huout) v).mpr hpuv
  apply (both_pairings_compatible_iff_block_noncrossing huv hab hbc hcd huval hvval).mp
  exact ⟨matching_related_pairs_no_cross m hm hmuv hmab,
    matching_related_pairs_no_cross m hm hmuv hmcd,
    matching_related_pairs_no_cross t ht htuv htad,
    matching_related_pairs_no_cross t ht htuv htbc⟩

theorem both_global_shapes_noncrossing {n : Nat} (m t p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hmref : ∀ i j, m i j → p i j) (htref : ∀ i j, t i j → p i j)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2)
    (hmab : m a b) (hmcd : m c d) (htad : t a d) (htbc : t b c) :
    PatternNoncrossing p := by
  intro w x y z hwx hxy hyz hpwy hpxz
  by_contra hn
  by_cases haw : p a w
  · have hay := p.trans haw hpwy
    have hxout : ¬ p a x := fun h => hn (p.trans (p.symm haw) h)
    have hno := both_shapes_external_pair_no_cross m t p hm ht hmref htref
      hab hbc hcd hclass hrest hmab hmcd htad htbc (lt_trans hxy hyz) hpxz hxout
    have hwcase := (four_class_rel_iff p hclass w).mp haw
    have hycase := (four_class_rel_iff p hclass y).mp hay
    apply hno
    unfold FourBlockCross
    omega
  · by_cases hax : p a x
    · have haz := p.trans hax hpxz
      have hno := both_shapes_external_pair_no_cross m t p hm ht hmref htref
        hab hbc hcd hclass hrest hmab hmcd htad htbc (lt_trans hwx hxy) hpwy haw
      have hxcase := (four_class_rel_iff p hclass x).mp hax
      have hzcase := (four_class_rel_iff p hclass z).mp haz
      apply hno
      unfold FourBlockCross
      omega
    · have hmwy := (matching_refinement_forced_pair m p hm hmref w (hrest w haw) y).mpr hpwy
      have hmxz := (matching_refinement_forced_pair m p hm hmref x (hrest x hax) z).mpr hpxz
      exact hm.2 w x y z hwx hxy hyz ⟨hmwy, hmxz⟩

theorem matching_refinement_has_representation {n : Nat} (m p : ColorPattern n)
    (hm : NoncrossingPairPattern m) (href : ∀ i j, m i j → p i j)
    (a : Fin n) (ha : (patternClassPositions p a).card = 4)
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2) :
    ∃ r : FourfoldMatchingRepresentation n, fourfoldRepresentationPattern r = p ∧ r.1.val = m := by
  classical
  let chosen := matchingClassesInside m p a
  have hcard : chosen.card = 2 := four_class_contains_two_matching_classes m p hm href a ha
  exact ⟨⟨⟨m, hm⟩, ⟨chosen, hcard⟩⟩, merge_matching_classes_recovers m p hm href a hrest, rfl⟩

/-- Conventional noncrossing permits both internal splits of its
four-position class, giving both global matching representations. -/
theorem noncrossing_fourfold_has_both_shapes {n : Nat} (p : ColorPattern n)
    (hnc : PatternNoncrossing p) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (ha : (patternClassPositions p a).card = 4)
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2) :
    ∃ r s : FourfoldMatchingRepresentation n,
      fourfoldRepresentationPattern r = p ∧ fourfoldRepresentationPattern s = p ∧
      r.1.val a b ∧ r.1.val c d ∧ s.1.val a d ∧ s.1.val b c := by
  classical
  have hclass' : patternClassPositions p a = {a, d, b, c} := by
    rw [hclass]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hm : NoncrossingPairPattern (splitPairClass p a b) :=
    ⟨splitPairClass_classes_two p hclass hrest (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega),
      splitPairClass_no_alternation p hnc hab hbc hcd hclass hrest (Or.inl rfl)⟩
  have ht : NoncrossingPairPattern (splitPairClass p a d) :=
    ⟨splitPairClass_classes_two p hclass' hrest (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega),
      splitPairClass_no_alternation p hnc hab hbc hcd hclass hrest (Or.inr rfl)⟩
  obtain ⟨r, hrp, hrm⟩ := matching_refinement_has_representation (splitPairClass p a b) p
    hm (splitPairClass_refines p a b) a ha hrest
  obtain ⟨s, hsp, hst⟩ := matching_refinement_has_representation (splitPairClass p a d) p
    ht (splitPairClass_refines p a d) a ha hrest
  have hpab := (four_class_rel_iff p hclass b).mpr (Or.inr (Or.inl rfl))
  have hpad := (four_class_rel_iff p hclass d).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hmcd : splitPairClass p a b c d := by
    have hmem : d ∈ patternClassPositions (splitPairClass p a b) c := by
      rw [splitPairClass_complement_class p hclass (by omega) (by omega) (by omega) (by omega)]
      simp
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have htbc : splitPairClass p a d b c := by
    have hmem : c ∈ patternClassPositions (splitPairClass p a d) b := by
      rw [splitPairClass_complement_class p hclass' (by omega) (by omega) (by omega) (by omega)]
      simp
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  refine ⟨r, s, hrp, hsp, ?_, ?_, ?_, ?_⟩
  · rw [hrm]
    exact splitPairClass_cut_related p hpab
  · rw [hrm]
    exact hmcd
  · rw [hst]
    exact splitPairClass_cut_related p hpad
  · rw [hst]
    exact htbc

/-- Exact geometric identification of the actual double fibers.
Noncrossing here compares distinct color classes and allows a four-block. -/
theorem fourfold_double_fiber_iff_noncrossing {n : Nat} (p : ColorPattern n)
    (hp : FourfoldPairPattern p) :
    (fourfoldRepresentationFiber p).card = 2 ↔ PatternNoncrossing p := by
  classical
  obtain ⟨a, b, c, d, hab, hbc, hcd, hclass, hrest⟩ := ordered_fourfold_profile p hp
  constructor
  · intro hdbl
    obtain ⟨r, s, hrp, hsp, hrab, hrcd, hsad, hsbc⟩ :=
      (fourfold_double_fiber_iff_both_shapes p hp hab hbc hcd hclass hrest).mp hdbl
    exact both_global_shapes_noncrossing r.1.val s.1.val p r.1.property s.1.property
      (fourfold_representation_refines r p hrp) (fourfold_representation_refines s p hsp)
      hab hbc hcd hclass hrest hrab hrcd hsad hsbc
  · intro hnc
    have hpab := (four_class_rel_iff p hclass b).mpr (Or.inr (Or.inl rfl))
    have hpac := (four_class_rel_iff p hclass c).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hpad := (four_class_rel_iff p hclass d).mpr (Or.inr (Or.inr (Or.inr rfl)))
    have hge := four_related_positions_card_ge_four p hab hbc hcd hpab hpac hpad
    have ha : (patternClassPositions p a).card = 4 := by
      rcases fourfold_profile_small_classes p hp a with h | h
      · omega
      · exact h
    apply (fourfold_double_fiber_iff_both_shapes p hp hab hbc hcd hclass hrest).mpr
    exact noncrossing_fourfold_has_both_shapes p hnc hab hbc hcd hclass ha hrest

#print axioms both_global_shapes_noncrossing
#print axioms noncrossing_fourfold_has_both_shapes
#print axioms fourfold_double_fiber_iff_noncrossing

end LC004
