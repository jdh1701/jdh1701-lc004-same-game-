import LC004.FourGapIndicator

namespace LC004
open scoped Classical

/-- The original four-class is fixed in the upper pattern, but the input may
split it arbitrarily. This is the refinement-ideal form needed by inversion. -/
theorem winning_iff_pairing_witnesses_below {n : Nat} (p r : ColorPattern n)
    (hrp : r ≤ p) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d}) :
    WinningColorPattern r ↔ PairingWitness r a b c d ∨ PairingWitness r a d b c := by
  constructor
  · rintro ⟨cert⟩
    let up := cert.recolor (patternColor p) (fun i j h =>
      (patternColor_eq_iff p i j).mpr (hrp ((patternColor_eq_iff r i j).mp h)))
    have heq : certificateBlockPattern up = certificateBlockPattern cert := rfl
    have hmem (i : Fin n) (hi : i ∈ ({a,b,c,d} : Finset (Fin n))) : p a i := by
      have : i ∈ patternClassPositions p a := hclass.symm ▸ hi
      simpa [patternClassPositions] using this
    have hfour : (patternClassPositions p a).card = 4 := by
      rw [hclass]
      have : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by omega
      simp [this.1,this.2.1,this.2.2.1,this.2.2.2.1,this.2.2.2.2.1,this.2.2.2.2.2]
    have htwo (i : Fin n) (hi : p a i) :
        (patternClassPositions (certificateBlockPattern cert) i).card = 2 := by
      rw [← heq]
      apply certificate_four_class_card p up i
      rw [← patternClassPositions_eq_of_related p hi]
      exact hfour
    have href : certificateBlockPattern cert ≤ r :=
      fun _ _ h => certificateBlockPattern_refines r cert h
    have shapes := certificate_four_two_shapes p up hab hbc hcd hclass
    rw [heq] at shapes
    rcases shapes with hs | ht
    · exact Or.inl ⟨_,certificateBlockPattern_constraint cert,href,hs.1,hs.2,
        htwo a (p.refl a),htwo c (hmem c (by simp))⟩
    · exact Or.inr ⟨_,certificateBlockPattern_constraint cert,href,ht.1,ht.2,
        htwo a (p.refl a),htwo b (hmem b (by simp))⟩
  · rintro (⟨q,hq,hqr,_⟩ | ⟨q,hq,hqr,_⟩) <;>
      exact (winning_iff_constraint_refinement r).mpr ⟨q,hq,hqr⟩

theorem pairing_overlap_below_iff {n : Nat} (r : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (PairingWitness r a b c d ∧ PairingWitness r a d b c) ↔
      r a b ∧ r a c ∧ r a d ∧ FourGapsWin r a b c d := by
  constructor
  · intro h
    obtain ⟨q,_,hqr,hqab,hqcd,_⟩ := h.1
    obtain ⟨t,_,htr,htad,htbc,_⟩ := h.2
    exact ⟨hqr hqab,r.trans (hqr hqab) (htr htbc),htr htad,
      two_pairing_witnesses_give_four_gaps r hab hbc hcd h.1 h.2⟩
  · rintro ⟨hrab,hrac,hrad,hg⟩
    exact (four_gap_overlap_iff r hab hbc hcd hrab hrac hrad).mpr hg

theorem four_gap_indicator_below {n : Nat} (p r : ColorPattern n)
    (hrp : r ≤ p) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d}) :
    (if WinningColorPattern r then (1 : Int) else 0) -
      (if WinningColorPattern (splitOffPair r c d) then 1 else 0) -
      (if WinningColorPattern (splitOffPair r b c) then 1 else 0) =
        -(if r a b ∧ r a c ∧ r a d ∧ FourGapsWin r a b c d then 1 else 0) := by
  have hcover (x : Fin n) (hx : r a x) : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hmem : x ∈ patternClassPositions p a := by
      simpa [patternClassPositions] using hrp hx
    rw [hclass] at hmem
    simpa using hmem
  rw [winning_splitOffPair_iff r a b c d (by omega) (by omega) (by omega) (by omega) hcover]
  rw [winning_splitOffPair_iff r a d b c (by omega) (by omega) (by omega) (by omega)
    (fun x hx => by have h := hcover x hx; tauto)]
  simp only [winning_iff_pairing_witnesses_below p r hrp hab hbc hcd hclass,
    ← pairing_overlap_below_iff r hab hbc hcd]
  by_cases hs : PairingWitness r a b c d <;>
    by_cases ht : PairingWitness r a d b c <;> simp [hs,ht]

#print axioms winning_iff_pairing_witnesses_below
#print axioms pairing_overlap_below_iff
#print axioms four_gap_indicator_below
end LC004
