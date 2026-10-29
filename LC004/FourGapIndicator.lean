import LC004.FourGapAssembly

namespace LC004
open scoped Classical

noncomputable def splitOffPair {n : Nat} (p : ColorPattern n) (c d : Fin n) :
    ColorPattern n := p ⊓ Setoid.ker (fun x => decide (x = c ∨ x = d))

theorem winning_splitOffPair_iff {n : Nat} (p : ColorPattern n)
    (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hcover : ∀ x, p a x → x = a ∨ x = b ∨ x = c ∨ x = d) :
    WinningColorPattern (splitOffPair p c d) ↔ PairingWitness p a b c d := by
  constructor
  · intro h
    obtain ⟨q,hq,hqr⟩ := (winning_iff_constraint_refinement _).mp h
    have rel {x y : Fin n} (hxy : q x y) :
        p x y ∧ decide (x = c ∨ x = d) = decide (y = c ∨ y = d) := hqr hxy
    have ha := constraint_confined_pair q hq hab (fun x hx => by
      have hf := (rel hx).2
      have hn : ¬ (x = c ∨ x = d) := by
        have : decide (x = c ∨ x = d) = false := by simpa [hac,had] using hf.symm
        simpa using this
      rcases hcover x (rel hx).1 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hn (Or.inl h)).elim
      · exact (hn (Or.inr h)).elim)
    have hc := constraint_confined_pair q hq hcd (fun x hx => by
      have hf := (rel hx).2
      have : decide (x = c ∨ x = d) = true := by simpa using hf.symm
      simpa using this)
    exact ⟨q,hq,fun _ _ h => (rel h).1,ha.1,hc.1,ha.2,hc.2⟩
  · rintro ⟨q,hq,hqp,hqab,hqcd,hqa,hqc⟩
    apply (winning_iff_constraint_refinement _).mpr
    refine ⟨q,hq,?_⟩
    intro x y hxy
    have closed (x y : Fin n) (hx : x = c ∨ x = d) (hxy : q x y) : y = c ∨ y = d := by
      have hcx : q c x := by rcases hx with rfl | rfl; exact q.refl _; exact hqcd
      exact (local_pair_rel_iff q hqc hcd hqcd y).mp (q.trans hcx hxy)
    change p x y ∧ decide (x = c ∨ x = d) = decide (y = c ∨ y = d)
    refine ⟨hqp hxy,?_⟩
    have hi : (x = c ∨ x = d) ↔ (y = c ∨ y = d) :=
      ⟨fun hx => closed x y hx hxy,fun hy => closed y x hy (q.symm hxy)⟩
    by_cases hx : x = c ∨ x = d
    · simp [hx,hi.mp hx]
    · have hy : ¬ (y = c ∨ y = d) := fun h => hx (hi.mpr h)
      simp [hx,hy]

/-- Exact integer overlap correction, stated on actual winning color patterns.
The two subtracted indicators split the four-occurrence class into its two
noncrossing pairings. No equality of their external certificates is assumed. -/
theorem four_gap_winning_indicator {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d}) :
    (if WinningColorPattern p then (1 : Int) else 0) -
      (if WinningColorPattern (splitOffPair p c d) then 1 else 0) -
      (if WinningColorPattern (splitOffPair p b c) then 1 else 0) =
        -(if FourGapsWin p a b c d then 1 else 0) := by
  have hcover (x : Fin n) (hx : p a x) : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hmem : x ∈ patternClassPositions p a := by simpa [patternClassPositions] using hx
    rw [hclass] at hmem
    simpa using hmem
  have hpa (x : Fin n) (hx : x ∈ ({a,b,c,d} : Finset (Fin n))) : p a x := by
    have : x ∈ patternClassPositions p a := hclass.symm ▸ hx
    simpa [patternClassPositions] using this
  rw [winning_splitOffPair_iff p a b c d (by omega) (by omega) (by omega) (by omega) hcover]
  rw [winning_splitOffPair_iff p a d b c (by omega) (by omega) (by omega) (by omega)
    (fun x hx => by have h := hcover x hx; tauto)]
  rw [winning_iff_two_pairing_witnesses p hab hbc hcd hclass,
    ← four_gap_overlap_iff p hab hbc hcd (hpa b (by simp)) (hpa c (by simp)) (hpa d (by simp))]
  by_cases hs : PairingWitness p a b c d <;>
    by_cases ht : PairingWitness p a d b c <;> simp [hs,ht]

#print axioms winning_splitOffPair_iff
#print axioms four_gap_winning_indicator
end LC004
