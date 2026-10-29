import LC004.ExceptionalDegreeProfiles

namespace LC004

theorem patternClassPositions_card_pos {n : Nat} (p : ColorPattern n) (i : Fin n) :
    0 < (patternClassPositions p i).card := by
  classical
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.refl i⟩⟩

theorem opening_degree_at_leader {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternOpeningDegree p (patternClassLeader p i) = (patternClassPositions p i).card := by
  exact (patternOpeningDegree_at_minimum p (Quotient.mk p i)).trans
    (congrArg Finset.card (patternQuotientFiber_mk_eq_class p i))

theorem class_card_of_positive_degree {n : Nat} (p : ColorPattern n)
    (i : Fin n) (a : Nat) (ha : 0 < a) (hi : patternOpeningDegree p i = a) :
    (patternClassPositions p i).card = a := by
  have hleader := (opening_degree_pos_iff_leader p i).mp (by omega)
  have h := opening_degree_at_leader p i
  rw [hleader, hi] at h
  exact h.symm

theorem positive_patternDegreeWord_origin {n : Nat} (p : ColorPattern n)
    (i : Fin (n + 1)) (a : Nat) (ha : 0 < a) (hi : (patternDegreeWord p i).val = a) :
    ∃ j : Fin n, i = j.castSucc ∧ patternOpeningDegree p j = a := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ⟨j, rfl, (patternDegreeWord_castSucc p j).symm.trans hi⟩
  · simp only [patternDegreeWord_last, Fin.val_zero] at hi
    omega

theorem fourfold_iff_singleExceptionalWord {n : Nat} (p : ColorPattern n) :
    FourfoldPairPattern p ↔ SingleExceptionalWord (patternDegreeWord p) 4 := by
  classical
  constructor
  · rintro ⟨a, ha, hrest⟩
    let i := patternClassLeader p a
    have hi : patternOpeningDegree p i = 4 := (opening_degree_at_leader p a).trans ha
    refine ⟨i.castSucc, (patternDegreeWord_castSucc p i).trans hi, ?_⟩
    intro j hji
    rcases Fin.eq_castSucc_or_eq_last j with ⟨t, rfl⟩ | rfl
    · rw [patternDegreeWord_castSucc]
      by_cases ht : patternOpeningDegree p t = 0
      · exact Or.inl ht
      · right
        have hlead : patternClassLeader p t = t :=
          nonzero_patternOpeningDegree_minimum p t ht
        have hna : ¬ p a t := by
          intro hat
          have heq := (pattern_related_iff_leaders p a t).mp hat
          rw [hlead] at heq
          exact hji (congrArg Fin.castSucc heq.symm)
        have h := opening_degree_at_leader p t
        rw [hlead, hrest t hna] at h
        exact h
    · exact Or.inl (by simp only [patternDegreeWord_last, Fin.val_zero])
  · rintro ⟨i, hi, hrest⟩
    obtain ⟨a, rfl, ha⟩ := positive_patternDegreeWord_origin p i 4 (by omega) hi
    refine ⟨a, class_card_of_positive_degree p a 4 (by omega) ha, ?_⟩
    intro j hna
    let t := patternClassLeader p j
    have hne : t.castSucc ≠ a.castSucc := by
      intro h
      have heq : t = a := Fin.castSucc_injective h
      have hrel := patternClassLeader_related p j
      rw [heq] at hrel
      exact hna hrel
    have h := hrest t.castSucc hne
    rw [patternDegreeWord_castSucc, opening_degree_at_leader] at h
    rcases h with h | h
    · have hp := patternClassPositions_card_pos p j
      omega
    · exact h

theorem twoTriple_iff_doubleExceptionalWord {n : Nat} (p : ColorPattern n) :
    TwoTriplePairPattern p ↔ DoubleExceptionalWord (patternDegreeWord p) 3 := by
  classical
  constructor
  · rintro ⟨a, b, hab, ha, hb, hrest⟩
    let i := patternClassLeader p a
    let j := patternClassLeader p b
    have hij : i ≠ j := fun h => hab ((pattern_related_iff_leaders p a b).mpr h)
    have hi : patternOpeningDegree p i = 3 := (opening_degree_at_leader p a).trans ha
    have hj : patternOpeningDegree p j = 3 := (opening_degree_at_leader p b).trans hb
    refine ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective h),
      (patternDegreeWord_castSucc p i).trans hi, (patternDegreeWord_castSucc p j).trans hj, ?_⟩
    intro t hti htj
    rcases Fin.eq_castSucc_or_eq_last t with ⟨s, rfl⟩ | rfl
    · rw [patternDegreeWord_castSucc]
      by_cases hs : patternOpeningDegree p s = 0
      · exact Or.inl hs
      · right
        have hlead : patternClassLeader p s = s :=
          nonzero_patternOpeningDegree_minimum p s hs
        have hna : ¬ p a s := by
          intro has
          have heq := (pattern_related_iff_leaders p a s).mp has
          rw [hlead] at heq
          exact hti (congrArg Fin.castSucc heq.symm)
        have hnb : ¬ p b s := by
          intro hbs
          have heq := (pattern_related_iff_leaders p b s).mp hbs
          rw [hlead] at heq
          exact htj (congrArg Fin.castSucc heq.symm)
        have h := opening_degree_at_leader p s
        rw [hlead, hrest s hna hnb] at h
        exact h
    · exact Or.inl (by simp only [patternDegreeWord_last, Fin.val_zero])
  · rintro ⟨i, j, hij, hi, hj, hrest⟩
    obtain ⟨a, rfl, ha⟩ := positive_patternDegreeWord_origin p i 3 (by omega) hi
    obtain ⟨b, rfl, hb⟩ := positive_patternDegreeWord_origin p j 3 (by omega) hj
    have hla : patternClassLeader p a = a :=
      (opening_degree_pos_iff_leader p a).mp (by omega)
    have hlb : patternClassLeader p b = b :=
      (opening_degree_pos_iff_leader p b).mp (by omega)
    have hab : ¬ p a b := by
      intro h
      have heq := (pattern_related_iff_leaders p a b).mp h
      rw [hla, hlb] at heq
      exact hij (congrArg Fin.castSucc heq)
    refine ⟨a, b, hab, class_card_of_positive_degree p a 3 (by omega) ha,
      class_card_of_positive_degree p b 3 (by omega) hb, ?_⟩
    intro s hna hnb
    let t := patternClassLeader p s
    have hne (u : Fin n) (hu : ¬ p u s) : t.castSucc ≠ u.castSucc := by
      intro h
      have heq : t = u := Fin.castSucc_injective h
      have hrel := patternClassLeader_related p s
      rw [heq] at hrel
      exact hu hrel
    have h := hrest t.castSucc (hne a hna) (hne b hnb)
    rw [patternDegreeWord_castSucc, opening_degree_at_leader] at h
    rcases h with h | h
    · have hp := patternClassPositions_card_pos p s
      omega
    · exact h

#print axioms fourfold_iff_singleExceptionalWord
#print axioms twoTriple_iff_doubleExceptionalWord

end LC004
