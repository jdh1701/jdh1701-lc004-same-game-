import LC004.FourfoldCertificatePairs

namespace LC004

theorem certificate_blocks_eq_of_shared {n q : Nat} {color : Fin n → Fin q}
    (cert : Noncrossing23Certificate color) {b c : List (Fin n)}
    (hb : b ∈ cert.blocks) (hc : c ∈ cert.blocks)
    {i : Fin n} (hib : i ∈ b) (hic : i ∈ c) : b = c := by
  classical
  by_contra hne
  exact (List.disjoint_left.mp
    (disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hc hne)) hib hic

/-- The certificate's blocks themselves define a partition of positions.
This does not identify distinct blocks of the same original color. -/
def certificateBlockPattern {n q : Nat} {color : Fin n → Fin q}
    (cert : Noncrossing23Certificate color) : ColorPattern n where
  r i j := ∃ b ∈ cert.blocks, i ∈ b ∧ j ∈ b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨b, hb, hi⟩ := cert.cover_position i
      exact ⟨b, hb, hi, hi⟩
    · rintro i j ⟨b, hb, hi, hj⟩
      exact ⟨b, hb, hj, hi⟩
    · rintro i j k ⟨b, hb, hi, hj⟩ ⟨c, hc, hjc, hk⟩
      have heq := certificate_blocks_eq_of_shared cert hb hc hj hjc
      exact ⟨b, hb, hi, heq.symm ▸ hk⟩

theorem certificateBlockPattern_class {n q : Nat} {color : Fin n → Fin q}
    (cert : Noncrossing23Certificate color) {b : List (Fin n)}
    (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b) :
    patternClassPositions (certificateBlockPattern cert) i = b.toFinset := by
  classical
  ext j
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, List.mem_toFinset]
  constructor
  · rintro ⟨c, hc, hic, hjc⟩
    exact (certificate_blocks_eq_of_shared cert hc hb hic hi) ▸ hjc
  · intro hj
    exact ⟨b, hb, hi, hj⟩

theorem certificateBlockPattern_refines {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p)) {i j : Fin n}
    (h : certificateBlockPattern cert i j) : p i j := by
  obtain ⟨b, hb, hi, hj⟩ := h
  obtain ⟨a, ha⟩ := cert.monochromatic b hb
  exact (patternColor_eq_iff p i j).mp ((ha i hi).trans (ha j hj).symm)

/-- Any all-pair certificate recovers an actual noncrossing perfect
matching of original positions. -/
theorem certificateBlockPattern_pair_noncrossing {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    (hpairs : ∀ b ∈ cert.blocks, b.length = 2) :
    NoncrossingPairPattern (certificateBlockPattern cert) := by
  classical
  constructor
  · intro i
    obtain ⟨b, hb, hi⟩ := cert.cover_position i
    have hc : (patternClassPositions (certificateBlockPattern cert) i).card = 2 := by
      rw [certificateBlockPattern_class cert hb hi,
        List.toFinset_card_of_nodup ((List.nodup_flatten.mp cert.flatten_nodup).1 b hb),
        hpairs b hb]
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using hc
  · rintro a b c d hab hbc hcd ⟨⟨ablock, ha, hap, hcp⟩, ⟨bblock, hb, hbp, hdp⟩⟩
    exact cert.no_alternation ha hb hap hcp hbp hdp (Or.inl ⟨hab, hbc, hcd⟩)

/-- First reconstruction step for the fourfold surjectivity theorem:
every winning fourfold pattern has a noncrossing matching refinement.
Recovering the two selected matching classes is still a separate step. -/
theorem fourfold_winning_has_pair_refinement {n : Nat} (p : ColorPattern n)
    (hprofile : FourfoldPairPattern p) (hwin : WinningColorPattern p) :
    ∃ m : ColorPattern n, NoncrossingPairPattern m ∧
      ∀ i j, m i j → p i j := by
  obtain ⟨cert⟩ := hwin
  exact ⟨certificateBlockPattern cert,
    certificateBlockPattern_pair_noncrossing cert (fourfold_certificate_all_pairs p hprofile cert),
    fun _ _ h => certificateBlockPattern_refines p cert h⟩

#print axioms certificateBlockPattern_pair_noncrossing
#print axioms fourfold_winning_has_pair_refinement

end LC004
