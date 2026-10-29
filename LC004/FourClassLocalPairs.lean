import LC004.HeavyFaceRestriction

namespace LC004

/-- A certificate block inside ONE four-occurrence color class is a pair.
No size restriction is imposed on any other color class. -/
theorem certificate_four_class_block_length {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {b : List (Fin n)} (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b)
    (hclass : (patternClassPositions p i).card = 4) : b.length = 2 := by
  classical
  rcases cert.sizes b hb with htwo | hthree
  · exact htwo
  · exfalso
    have hsub := certificate_block_subset_class p cert hb hi
    have hbn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
    have hbc : b.toFinset.card = 3 := by rw [List.toFinset_card_of_nodup hbn, hthree]
    have hdiff : ((patternClassPositions p i) \ b.toFinset).card = 1 := by
      rw [Finset.card_sdiff hsub, hclass, hbc]
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 <
      ((patternClassPositions p i) \ b.toFinset).card by omega)
    have hjc := (Finset.mem_sdiff.mp hj).1
    have hjnot := (Finset.mem_sdiff.mp hj).2
    have hij : p i j := by
      simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using hjc
    obtain ⟨c, hc, hjmem⟩ := cert.cover_position j
    have hne : b ≠ c := by
      intro heq
      apply hjnot
      exact List.mem_toFinset.mpr (heq.symm ▸ hjmem)
    have hdis := disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hc hne
    have hcsub : c.toFinset ⊆ (patternClassPositions p i) \ b.toFinset := by
      intro x hx
      have hxc := List.mem_toFinset.mp hx
      have hjx : p j x := by
        have h := certificate_block_subset_class p cert hc hjmem hx
        simpa only [patternClassPositions, Finset.mem_filter,
          Finset.mem_univ, true_and] using h
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa only [patternClassPositions, Finset.mem_filter,
          Finset.mem_univ, true_and] using p.trans hij hjx
      · intro hxb
        exact (List.disjoint_left.mp hdis) (List.mem_toFinset.mp hxb) hxc
    have hcle := Finset.card_le_card hcsub
    have hcn := (List.nodup_flatten.mp cert.flatten_nodup).1 c hc
    have hclen := cert.sizes c hc
    rw [List.toFinset_card_of_nodup hcn, hdiff] at hcle
    rcases hclen with h | h <;> omega

theorem certificate_four_class_card {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p)) (i : Fin n)
    (hclass : (patternClassPositions p i).card = 4) :
    (patternClassPositions (certificateBlockPattern cert) i).card = 2 := by
  obtain ⟨b, hb, hi⟩ := cert.cover_position i
  rw [certificateBlockPattern_class cert hb hi,
    List.toFinset_card_of_nodup ((List.nodup_flatten.mp cert.flatten_nodup).1 b hb)]
  exact certificate_four_class_block_length p cert hb hi hclass

#print axioms certificate_four_class_block_length
#print axioms certificate_four_class_card
end LC004
