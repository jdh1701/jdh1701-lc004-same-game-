import LC004.FourfoldFiberCount

namespace LC004

/-- The actual global fiber is doubled exactly when the separated and
nested internal shapes are both realized by global noncrossing matchings.
The further geometric identification with coarse noncrossing partitions
is not asserted by this theorem. -/
theorem fourfold_double_fiber_iff_both_shapes {n : Nat} (p : ColorPattern n)
    (hp : FourfoldPairPattern p) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a, b, c, d})
    (hrest : ∀ i, ¬ p a i → (patternClassPositions p i).card = 2) :
    (fourfoldRepresentationFiber p).card = 2 ↔
      ∃ r s : FourfoldMatchingRepresentation n,
        fourfoldRepresentationPattern r = p ∧ fourfoldRepresentationPattern s = p ∧
        r.1.val a b ∧ r.1.val c d ∧ s.1.val a d ∧ s.1.val b c := by
  classical
  have hclass' : patternClassPositions p a = {a, d, b, c} := by
    rw [hclass]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  constructor
  · intro hcard
    obtain ⟨r, s, hne, hset⟩ := Finset.card_eq_two.mp hcard
    have hrmem : r ∈ fourfoldRepresentationFiber p := by rw [hset]; simp
    have hsmem : s ∈ fourfoldRepresentationFiber p := by rw [hset]; simp
    have hrp : fourfoldRepresentationPattern r = p := (Finset.mem_filter.mp hrmem).2
    have hsp : fourfoldRepresentationPattern s = p := (Finset.mem_filter.mp hsmem).2
    have href := fourfold_representation_refines r p hrp
    have hsref := fourfold_representation_refines s p hsp
    have hrsh := four_refinement_two_shapes r.1.val p r.1.property href hab hbc hcd hclass
    have hssh := four_refinement_two_shapes s.1.val p s.1.property hsref hab hbc hcd hclass
    rcases hrsh with hrsep | hrnest
    · rcases hssh with hssep | hsnest
      · have hm := matching_refinements_eq_of_pairs r.1.val s.1.val p
          r.1.property s.1.property href hsref (by omega) (by omega) hclass hrest
          hrsep.1 hrsep.2 hssep.1 hssep.2
        exact (hne (fourfold_representations_eq_of_matching r s hm (hrp.trans hsp.symm))).elim
      · exact ⟨r, s, hrp, hsp, hrsep.1, hrsep.2, hsnest.1, hsnest.2⟩
    · rcases hssh with hssep | hsnest
      · exact ⟨s, r, hsp, hrp, hssep.1, hssep.2, hrnest.1, hrnest.2⟩
      · have hm := matching_refinements_eq_of_pairs r.1.val s.1.val p
          r.1.property s.1.property href hsref (by omega) (by omega) hclass' hrest
          hrnest.1 hrnest.2 hsnest.1 hsnest.2
        exact (hne (fourfold_representations_eq_of_matching r s hm (hrp.trans hsp.symm))).elim
  · rintro ⟨r, s, hrp, hsp, hrab, _, hsad, _⟩
    have hne : r ≠ s := by
      intro heq
      subst s
      have hbad := (pair_pattern_rel_iff r.1.val r.1.property
        (show a ≠ d by omega) hsad b).mp hrab
      rcases hbad with h | h <;> omega
    have hrmem : r ∈ fourfoldRepresentationFiber p := by simp [fourfoldRepresentationFiber, hrp]
    have hsmem : s ∈ fourfoldRepresentationFiber p := by simp [fourfoldRepresentationFiber, hsp]
    have hsub : ({r, s} : Finset (FourfoldMatchingRepresentation n)) ⊆
        fourfoldRepresentationFiber p := by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        exact hrmem
      · have ht' := Finset.mem_singleton.mp ht
        subst t
        exact hsmem
    have hle := Finset.card_le_card hsub
    have hpair : ({r, s} : Finset (FourfoldMatchingRepresentation n)).card = 2 := by simp [hne]
    have hbound := fourfold_representation_fiber_le_two p hp
    omega

#print axioms fourfold_double_fiber_iff_both_shapes

end LC004
