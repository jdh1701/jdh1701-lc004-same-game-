import LC004.FourGapWitnessOverlap

namespace LC004
open scoped Classical

theorem winning_mono_pair {n : Nat} (p : ColorPattern n) {a b : Fin n}
    (hne : a ≠ b) (hab : p a b) :
    WinningColorPattern (restrictColorPattern p
      (({a,b} : Finset (Fin n)).orderEmbOfFin rfl)) := by
  let S : Finset (Fin n) := {a,b}
  let e := S.orderEmbOfFin rfl
  let q := restrictColorPattern p e
  have hq (i j : Fin S.card) : q i j := by
    apply (restrictColorPattern_rel p e i j).mpr
    have hi := S.orderEmbOfFin_mem rfl i
    have hj := S.orderEmbOfFin_mem rfl j
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      rw [hi,hj] <;> first | exact p.refl _ | exact hab | exact p.symm hab
  have hc (i : Fin S.card) : (patternClassPositions q i).card = 2 := by
    have he : patternClassPositions q i = Finset.univ := by
      ext j
      simp [patternClassPositions,hq]
    rw [he]
    simp [S,hne]
  exact (winning_small_pattern_iff_noncrossing q (fun i => Or.inl (hc i))).mpr
    (fun i j _ _ _ _ _ _ _ => hq i j)

theorem constraint_confined_pair {n : Nat} (q : ColorPattern n)
    (hq : CertificateConstraint q) {a b : Fin n} (hne : a ≠ b)
    (hconf : ∀ x, q a x → x = a ∨ x = b) :
    q a b ∧ (patternClassPositions q a).card = 2 := by
  classical
  have hs : patternClassPositions q a ⊆ ({a,b} : Finset (Fin n)) := by
    intro x hx
    have h : q a x := by simpa [patternClassPositions] using hx
    simpa using hconf x h
  have hcard := Finset.card_le_card hs
  have hsize := hq.1 a
  have hp : (patternClassPositions q a).card = 2 := by
    simp only [Finset.card_pair hne] at hcard
    omega
  have he : patternClassPositions q a = {a,b} :=
    Finset.eq_of_subset_of_card_le hs (by simp [hp,hne])
  have hb : b ∈ patternClassPositions q a := by rw [he]; simp
  exact ⟨by simpa [patternClassPositions] using hb,hp⟩

/-- Assemble both pairing witnesses from the four winning gaps. -/
theorem four_gaps_give_pairing_witness {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hpab : p a b) (hpac : p a c) (hpad : p a d)
    (hg : FourGapsWin p a b c d) (nested : Bool) :
    if nested then PairingWitness p a d b c else PairingWitness p a b c d := by
  classical
  let S := fourPairRegions nested a b c d
  let e := fun k : Fin 6 => (S k).orderEmbOfFin rfl
  have cover : ∀ x, ∃ k i, e k i = x := by
    intro x
    obtain ⟨k,hk⟩ := fourPairRegions_cover nested hab hbc hcd x
    refine ⟨k,?_⟩
    have hr : x ∈ Set.range (e k) := by
      change x ∈ Set.range ((S k).orderEmbOfFin rfl)
      rwa [Finset.range_orderEmbOfFin]
    exact hr
  have disjoint : ∀ k l i j, e k i = e l j → k = l := by
    intro k l i j hij
    apply fourPairRegions_disjoint nested hab hbc hcd k l (e k i)
      ((S k).orderEmbOfFin_mem rfl i)
    rw [hij]
    exact (S l).orderEmbOfFin_mem rfl j
  have nc : ∀ k l i j s t,
      e k i < e l s → e l s < e k j → e k j < e l t → k = l := by
    intro k l i j s t h1 h2 h3
    exact fourPairRegions_noncrossing nested hab hbc hcd k l _ _ _ _ h1 h2 h3
      ((S k).orderEmbOfFin_mem rfl i) ((S k).orderEmbOfFin_mem rfl j)
      ((S l).orderEmbOfFin_mem rfl s) ((S l).orderEmbOfFin_mem rfl t)
  have hw : ∀ k, WinningColorPattern (restrictColorPattern p (e k)) := by
    intro k
    fin_cases k
    · cases nested
      · exact winning_mono_pair p (by omega) hpab
      · exact winning_mono_pair p (by omega) hpad
    · cases nested
      · exact winning_mono_pair p (by omega) (p.trans (p.symm hpac) hpad)
      · exact winning_mono_pair p (by omega) (p.trans (p.symm hpab) hpac)
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2.1
    · exact hg.2.2.2
  let r := assembledPattern e (fun k => restrictColorPattern p (e k)) cover disjoint
  have hrp : r ≤ p := by
    rintro x y ⟨k,i,j,rfl,rfl,h⟩
    exact (restrictColorPattern_rel p (e k) i j).mp h
  have heq (k : Fin 6) : restrictColorPattern r (e k) = restrictColorPattern p (e k) := by
    apply Setoid.ext
    intro i j
    exact (restrictColorPattern_rel r (e k) i j).trans
      (assembledPattern_local e _ cover disjoint k i j)
  have hrwin : WinningColorPattern r :=
    winning_of_ordered_region_cover r _ e cover disjoint nc
      (fun k => by rw [heq]; exact hw k)
  obtain ⟨q,hq,hqr⟩ := (winning_iff_constraint_refinement r).mp hrwin
  have confined (k : Fin 6) (x : Fin n) (hx : x ∈ S k)
      (y : Fin n) (hxy : q x y) : y ∈ S k := by
    obtain ⟨l,i,j,hi,hj,_⟩ := hqr hxy
    have hx' : x ∈ S l := by rw [← hi]; exact (S l).orderEmbOfFin_mem rfl i
    have hkl := fourPairRegions_disjoint nested hab hbc hcd k l x hx hx'
    subst l
    rw [← hj]
    exact (S k).orderEmbOfFin_mem rfl j
  have hqp : q ≤ p := le_trans hqr hrp
  cases nested
  · have ha := constraint_confined_pair q hq (show a ≠ b by omega)
      (fun x hx => by simpa [S,fourPairRegions] using confined 0 a (by simp [S,fourPairRegions]) x hx)
    have hc := constraint_confined_pair q hq (show c ≠ d by omega)
      (fun x hx => by simpa [S,fourPairRegions] using confined 1 c (by simp [S,fourPairRegions]) x hx)
    exact ⟨q,hq,hqp,ha.1,hc.1,ha.2,hc.2⟩
  · have ha := constraint_confined_pair q hq (show a ≠ d by omega)
      (fun x hx => by simpa [S,fourPairRegions] using confined 0 a (by simp [S,fourPairRegions]) x hx)
    have hb := constraint_confined_pair q hq (show b ≠ c by omega)
      (fun x hx => by simpa [S,fourPairRegions] using confined 1 b (by simp [S,fourPairRegions]) x hx)
    exact ⟨q,hq,hqp,ha.1,hb.1,ha.2,hb.2⟩

theorem four_gap_overlap_iff {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hpab : p a b) (hpac : p a c) (hpad : p a d) :
    (PairingWitness p a b c d ∧ PairingWitness p a d b c) ↔ FourGapsWin p a b c d := by
  constructor
  · exact fun h => two_pairing_witnesses_give_four_gaps p hab hbc hcd h.1 h.2
  · intro h
    exact ⟨four_gaps_give_pairing_witness p hab hbc hcd hpab hpac hpad h false,
      four_gaps_give_pairing_witness p hab hbc hcd hpab hpac hpad h true⟩

#print axioms four_gaps_give_pairing_witness
#print axioms four_gap_overlap_iff
end LC004
