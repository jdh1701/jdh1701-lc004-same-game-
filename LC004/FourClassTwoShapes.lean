import LC004.FourClassLocalPairs

namespace LC004

theorem local_pair_rel_iff {n : Nat} (m : ColorPattern n)
    {a b : Fin n} (hsize : (patternClassPositions m a).card = 2)
    (hne : a ≠ b) (hab : m a b) (x : Fin n) :
    m a x ↔ x = a ∨ x = b := by
  classical
  have hsub : ({a,b} : Finset (Fin n)) ⊆ patternClassPositions m a := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
        true_and] using m.refl y
    · have : y = b := Finset.mem_singleton.mp hy
      subst y
      simp [patternClassPositions, hab]
  have heq : ({a,b} : Finset (Fin n)) = patternClassPositions m a :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hsize, hne])
  have hmem := congrArg (fun S : Finset (Fin n) => x ∈ S) heq
  simpa [patternClassPositions] using (Iff.of_eq hmem).symm

theorem local_pair_other {n : Nat} (m : ColorPattern n) (a : Fin n)
    (hsize : (patternClassPositions m a).card = 2) :
    ∃ b, b ≠ a ∧ m a b := by
  classical
  obtain ⟨b,hb,hne⟩ := Finset.exists_mem_ne
    (show 1 < (patternClassPositions m a).card by omega) a
  exact ⟨b,hne,by simpa [patternClassPositions] using hb⟩

theorem local_four_complement {n : Nat} (m p : ColorPattern n) (href : m ≤ p)
    {a b c d : Fin n}
    (hsizea : (patternClassPositions m a).card = 2)
    (hsizec : (patternClassPositions m c).card = 2)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hcover : ∀ x, p a x → x = a ∨ x = b ∨ x = c ∨ x = d)
    (hac : p a c) (hmatch : m a b) : m c d := by
  have hnca : ¬ m c a := by
    intro h
    rcases (local_pair_rel_iff m hsizea hab hmatch c).mp (m.symm h) with h | h
    · exact hca h
    · exact hcb h
  obtain ⟨x,hxc,hcx⟩ := local_pair_other m c hsizec
  rcases hcover x (p.trans hac (href hcx)) with h | h | h | h
  · subst x
    exact (hnca hcx).elim
  · subst x
    exact (hnca (m.trans hcx (m.symm hmatch))).elim
  · exact (hxc h).elim
  · exact h ▸ hcx

/-- Two pairing shapes for a single four-occurrence color. Other colors may
have arbitrary multiplicities and their certificate blocks may be triples. -/
theorem certificate_four_two_shapes {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d}) :
    let m := certificateBlockPattern cert
    (m a b ∧ m c d) ∨ (m a d ∧ m b c) := by
  classical
  let m := certificateBlockPattern cert
  change (m a b ∧ m c d) ∨ (m a d ∧ m b c)
  have href : m ≤ p := fun _ _ h => certificateBlockPattern_refines p cert h
  have hcover (x : Fin n) (hx : p a x) : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hmem : x ∈ patternClassPositions p a := by simp [patternClassPositions, hx]
    rw [hclass] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hpa (x : Fin n) (hx : x ∈ ({a,b,c,d} : Finset (Fin n))) : p a x := by
    have hmem : x ∈ patternClassPositions p a := hclass.symm ▸ hx
    simpa [patternClassPositions] using hmem
  have hfour : (patternClassPositions p a).card = 4 := by
    rw [hclass]
    have : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by omega
    simp [this.1,this.2.1,this.2.2.1,this.2.2.2.1,this.2.2.2.2.1,this.2.2.2.2.2]
  have htwo (i : Fin n) (hi : p a i) : (patternClassPositions m i).card = 2 := by
    apply certificate_four_class_card p cert i
    rw [← patternClassPositions_eq_of_related p hi]
    exact hfour
  have h2a := htwo a (p.refl a)
  have h2b := htwo b (hpa b (by simp))
  have h2c := htwo c (hpa c (by simp))
  obtain ⟨x,hxa,hax⟩ := local_pair_other m a h2a
  rcases hcover x (href hax) with h | h | h | h
  · exact (hxa h).elim
  · subst x
    exact Or.inl ⟨hax,local_four_complement m p href h2a h2c
      (by omega) (by omega) (by omega) hcover (hpa c (by simp)) hax⟩
  · subst x
    have hbd : m b d := local_four_complement m p href h2a h2b
      (by omega) (by omega) (by omega)
      (fun x hx => by have h := hcover x hx; tauto) (hpa b (by simp)) hax
    have hc := certificateBlockPattern_constraint cert
    have hno := small_noncrossing_no_alternation m
      (fun i => by
        have hs : (patternClassPositions m i).card = 2 ∨
          (patternClassPositions m i).card = 3 := hc.1 i
        omega) hc.2
    exact (hno a b c d hab hbc hcd ⟨hax,hbd⟩).elim
  · subst x
    exact Or.inr ⟨hax,local_four_complement m p href h2a h2b
      (by omega) (by omega) (by omega)
      (fun x hx => by have h := hcover x hx; tauto) (hpa b (by simp)) hax⟩

#print axioms certificate_four_two_shapes
end LC004
