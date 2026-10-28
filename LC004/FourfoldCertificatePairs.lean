import LC004.PairPatternCertificate

namespace LC004

theorem certificate_block_subset_class {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {b : List (Fin n)} (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b) :
    b.toFinset ⊆ patternClassPositions p i := by
  classical
  obtain ⟨a, ha⟩ := cert.monochromatic b hb
  intro j hj
  have hij : p i j := (patternColor_eq_iff p i j).mp
    ((ha i hi).trans (ha j (List.mem_toFinset.mp hj)).symm)
  simpa only [patternClassPositions, Finset.mem_filter,
    Finset.mem_univ, true_and] using hij

/-- With color classes of size two or four, a triple would leave a
single uncovered position of its color. Its certificate block must be
disjoint from the triple and have at least two positions: impossible. -/
theorem certificate_even_small_classes_all_pairs {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 4)
    (cert : Noncrossing23Certificate (patternColor p)) :
    ∀ b ∈ cert.blocks, b.length = 2 := by
  classical
  intro b hb
  rcases cert.sizes b hb with htwo | hthree
  · exact htwo
  · exfalso
    have hbne : b ≠ [] := by intro h; simp [h] at hthree
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil b hbne
    have hsub := certificate_block_subset_class p cert hb hi
    have hbn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
    have hbc : b.toFinset.card = 3 := by rw [List.toFinset_card_of_nodup hbn, hthree]
    have hclass : (patternClassPositions p i).card = 4 := by
      have hle := Finset.card_le_card hsub
      rcases hsmall i with h | h
      · omega
      · exact h
    have hdiff : ((patternClassPositions p i) \ b.toFinset).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hclass, hbc]
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

/-- Intrinsic fourfold-plus-pairs profile, independent of color labels. -/
def FourfoldPairPattern {n : Nat} (p : ColorPattern n) : Prop :=
  ∃ i, (patternClassPositions p i).card = 4 ∧
    ∀ j, ¬ p i j → (patternClassPositions p j).card = 2

theorem pattern_class_eq_of_related {n : Nat} (p : ColorPattern n)
    {i j : Fin n} (hij : p i j) :
    patternClassPositions p i = patternClassPositions p j := by
  classical
  ext x
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => p.trans (p.symm hij) h, fun h => p.trans hij h⟩

theorem fourfold_profile_small_classes {n : Nat} (p : ColorPattern n)
    (h : FourfoldPairPattern p) :
    ∀ j, (patternClassPositions p j).card = 2 ∨
      (patternClassPositions p j).card = 4 := by
  classical
  obtain ⟨i, hi, hrest⟩ := h
  intro j
  by_cases hij : p i j
  · right
    rw [← pattern_class_eq_of_related p hij]
    exact hi
  · exact Or.inl (hrest j hij)

theorem fourfold_certificate_all_pairs {n : Nat} (p : ColorPattern n)
    (h : FourfoldPairPattern p) (cert : Noncrossing23Certificate (patternColor p)) :
    ∀ b ∈ cert.blocks, b.length = 2 :=
  certificate_even_small_classes_all_pairs p (fourfold_profile_small_classes p h) cert

#print axioms certificate_even_small_classes_all_pairs
#print axioms fourfold_certificate_all_pairs

end LC004
