import LC004.CertificatePairRegions

namespace LC004
open scoped Classical

def PairingWitness {n : Nat} (p : ColorPattern n) (a b c d : Fin n) : Prop :=
  ∃ q : ColorPattern n, CertificateConstraint q ∧ q ≤ p ∧ q a b ∧ q c d ∧
    (patternClassPositions q a).card = 2 ∧ (patternClassPositions q c).card = 2

def FourGapsWin {n : Nat} (p : ColorPattern n) (a b c d : Fin n) : Prop :=
  WinningColorPattern (restrictColorPattern p ((pairInterior a b).orderEmbOfFin rfl)) ∧
  WinningColorPattern (restrictColorPattern p ((pairInterior b c).orderEmbOfFin rfl)) ∧
  WinningColorPattern (restrictColorPattern p ((pairInterior c d).orderEmbOfFin rfl)) ∧
  WinningColorPattern (restrictColorPattern p ((pairExterior a d).orderEmbOfFin rfl))

/-- The two witnesses may use entirely different external certificates. -/
theorem two_pairing_witnesses_give_four_gaps {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hs : PairingWitness p a b c d) (ht : PairingWitness p a d b c) :
    FourGapsWin p a b c d := by
  obtain ⟨q,hq,hqp,hqab,hqcd,hqa,hqc⟩ := hs
  obtain ⟨r,hr,hrp,hrad,hrbc,hra,hrb⟩ := ht
  exact ⟨winning_pair_interior p q hq hqp hab hqab hqa,
    winning_pair_interior p r hr hrp hbc hrbc hrb,
    winning_pair_interior p q hq hqp hcd hqcd hqc,
    winning_pair_exterior p r hr hrp (by omega) hrad hra⟩

theorem winning_iff_two_pairing_witnesses {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d}) :
    WinningColorPattern p ↔ PairingWitness p a b c d ∨ PairingWitness p a d b c := by
  constructor
  · rintro ⟨cert⟩
    have hmem (i : Fin n) (hi : i ∈ ({a,b,c,d} : Finset (Fin n))) : p a i := by
      have : i ∈ patternClassPositions p a := hclass.symm ▸ hi
      simpa [patternClassPositions] using this
    have hfour : (patternClassPositions p a).card = 4 := by
      rw [hclass]
      have : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by omega
      simp [this.1,this.2.1,this.2.2.1,this.2.2.2.1,this.2.2.2.2.1,this.2.2.2.2.2]
    have htwo (i : Fin n) (hi : p a i) :
        (patternClassPositions (certificateBlockPattern cert) i).card = 2 := by
      apply certificate_four_class_card p cert i
      rw [← patternClassPositions_eq_of_related p hi]
      exact hfour
    have href : certificateBlockPattern cert ≤ p :=
      fun _ _ h => certificateBlockPattern_refines p cert h
    rcases certificate_four_two_shapes p cert hab hbc hcd hclass with hs | ht
    · exact Or.inl ⟨_,certificateBlockPattern_constraint cert,href,hs.1,hs.2,
        htwo a (p.refl a),htwo c (hmem c (by simp))⟩
    · exact Or.inr ⟨_,certificateBlockPattern_constraint cert,href,ht.1,ht.2,
        htwo a (p.refl a),htwo b (hmem b (by simp))⟩
  · rintro (⟨q,hq,hqp,_⟩ | ⟨q,hq,hqp,_⟩) <;>
      exact (winning_iff_constraint_refinement p).mpr ⟨q,hq,hqp⟩

noncomputable def fourPairRegions {n : Nat} (nested : Bool)
    (a b c d : Fin n) : Fin 6 → Finset (Fin n)
  | 0 => if nested then {a,d} else {a,b}
  | 1 => if nested then {b,c} else {c,d}
  | 2 => pairInterior a b
  | 3 => pairInterior b c
  | 4 => pairInterior c d
  | 5 => pairExterior a d

theorem fourPairRegions_cover {n : Nat} (nested : Bool)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) (x : Fin n) :
    ∃ k, x ∈ fourPairRegions nested a b c d k := by
  by_contra h
  push_neg at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  cases nested <;>
    simp [fourPairRegions,pairInterior,pairExterior] at * <;> omega

theorem fourPairRegions_disjoint {n : Nat} (nested : Bool)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (k l : Fin 6) (x : Fin n)
    (hx : x ∈ fourPairRegions nested a b c d k)
    (hy : x ∈ fourPairRegions nested a b c d l) : k = l := by
  fin_cases k <;> fin_cases l <;> cases nested <;>
    simp [fourPairRegions,pairInterior,pairExterior] at * <;> omega

theorem fourPairRegions_noncrossing {n : Nat} (nested : Bool)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (k l : Fin 6) (u v w z : Fin n) (huv : u < v) (hvw : v < w) (hwz : w < z)
    (hu : u ∈ fourPairRegions nested a b c d k)
    (hw : w ∈ fourPairRegions nested a b c d k)
    (hv : v ∈ fourPairRegions nested a b c d l)
    (hz : z ∈ fourPairRegions nested a b c d l) : k = l := by
  fin_cases k <;> fin_cases l <;> cases nested <;>
    simp [fourPairRegions,pairInterior,pairExterior] at * <;> omega

#print axioms two_pairing_witnesses_give_four_gaps
#print axioms winning_iff_two_pairing_witnesses
#print axioms fourPairRegions_noncrossing
end LC004
