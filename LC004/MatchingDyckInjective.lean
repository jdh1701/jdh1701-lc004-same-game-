import LC004.MatchingDyckEncoding

namespace LC004

/-- If two noncrossing matchings have the same endpoint directions,
a differing right partner forces a disagreement at a later opening. -/
theorem later_open_disagreement {n : Nat} (m t : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hdir : ∀ i, (i < matchingPartner m hm i) ↔ (i < matchingPartner t ht i))
    (i : Fin n) (hi : i < matchingPartner m hm i)
    (hlt : matchingPartner m hm i < matchingPartner t ht i) :
    ∃ l, i < l ∧ l < matchingPartner m hm l ∧
      matchingPartner m hm l ≠ matchingPartner t ht l := by
  let j := matchingPartner m hm i
  let l := matchingPartner t ht j
  have hmj : matchingPartner m hm j = i := matchingPartner_twice m hm i
  have hjnot : ¬ j < matchingPartner m hm j := by
    rw [hmj]
    exact not_lt_of_ge (le_of_lt hi)
  have htjnot : ¬ j < matchingPartner t ht j := fun h => hjnot ((hdir j).mpr h)
  have hlj : l < j := by
    have hn := (matchingPartner_spec t ht j).1
    change matchingPartner t ht j < j
    omega
  have htl : matchingPartner t ht l = j := matchingPartner_twice t ht j
  have htlj : t l j := t.symm (matchingPartner_spec t ht j).2
  have htik := (matchingPartner_spec t ht i).2
  have hnli : ¬ l < i := by
    intro hli
    exact ht.2 l i j (matchingPartner t ht i) hli hi hlt ⟨htlj, htik⟩
  have hlne : l ≠ i := by
    intro heq
    have hh := congrArg (matchingPartner t ht) heq
    rw [htl] at hh
    exact (ne_of_lt hlt) hh
  have hil : i < l := by omega
  have hltopen : l < matchingPartner t ht l := by rw [htl]; exact hlj
  refine ⟨l, hil, (hdir l).mpr hltopen, ?_⟩
  intro heq
  have hh : matchingPartner m hm l = matchingPartner m hm i := heq.trans htl
  exact (ne_of_gt hil) (matchingPartner_injective m hm hh)

theorem matching_partners_eq_of_directions {n : Nat} (m t : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hdir : ∀ i, (i < matchingPartner m hm i) ↔ (i < matchingPartner t ht i)) :
    ∀ i, matchingPartner m hm i = matchingPartner t ht i := by
  classical
  have hopen : ∀ i, i < matchingPartner m hm i →
      matchingPartner m hm i = matchingPartner t ht i := by
    by_contra h
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    let s := (Finset.univ : Finset (Fin n)).filter
      (fun x => x < matchingPartner m hm x ∧ matchingPartner m hm x ≠ matchingPartner t ht x)
    have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hne⟩⟩
    let a := s.max' hs
    have ha : a ∈ s := Finset.max'_mem s hs
    have hap := (Finset.mem_filter.mp ha).2
    have hlater : ∃ l, a < l ∧ l < matchingPartner m hm l ∧
        matchingPartner m hm l ≠ matchingPartner t ht l := by
      rcases lt_or_gt_of_ne hap.2 with hlt | hgt
      · exact later_open_disagreement m t hm ht hdir a hap.1 hlt
      · obtain ⟨l, hal, hl, hne⟩ := later_open_disagreement t m ht hm
          (fun x => (hdir x).symm) a ((hdir a).mp hap.1) hgt
        exact ⟨l, hal, (hdir l).mpr hl, Ne.symm hne⟩
    obtain ⟨l, hal, hl, hlne⟩ := hlater
    have hlmem : l ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hlne⟩
    have hle : l ≤ a := Finset.le_max' s l hlmem
    exact (not_lt_of_ge hle) hal
  intro i
  by_cases hi : i < matchingPartner m hm i
  · exact hopen i hi
  · have hn := (matchingPartner_spec m hm i).1
    have hc : matchingPartner m hm i < i := by omega
    have hjopen : matchingPartner m hm i < matchingPartner m hm (matchingPartner m hm i) := by
      rw [matchingPartner_twice]
      exact hc
    have he := hopen (matchingPartner m hm i) hjopen
    rw [matchingPartner_twice] at he
    have hh := congrArg (matchingPartner t ht) he
    rw [matchingPartner_twice] at hh
    exact hh.symm

theorem matching_eq_of_directions {n : Nat} (m t : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (hdir : ∀ i, (i < matchingPartner m hm i) ↔ (i < matchingPartner t ht i)) : m = t := by
  have he := matching_partners_eq_of_directions m t hm ht hdir
  apply Setoid.ext
  intro i j
  rw [pair_pattern_rel_iff m hm (matchingPartner_spec m hm i).1.symm
      (matchingPartner_spec m hm i).2,
    pair_pattern_rel_iff t ht (matchingPartner_spec t ht i).1.symm
      (matchingPartner_spec t ht i).2, he i]

theorem matching_eq_of_dyck_encoding {n : Nat} (m t : ColorPattern n)
    (hm : NoncrossingPairPattern m) (ht : NoncrossingPairPattern t)
    (h : matchingToDyckWord m hm = matchingToDyckWord t ht) : m = t := by
  have hl : List.ofFn (matchingDyckStep m hm) = List.ofFn (matchingDyckStep t ht) :=
    congrArg DyckWord.toList h
  have hsteps := List.ofFn_injective hl
  apply matching_eq_of_directions m t hm ht
  intro i
  rw [← matchingDyckStep_U_iff m hm i, ← matchingDyckStep_U_iff t ht i, congrFun hsteps i]

theorem matchingDyckMap_injective (m : Nat) : Function.Injective (matchingDyckMap m) := by
  intro p t h
  apply Subtype.ext
  exact matching_eq_of_dyck_encoding p.val t.val p.property t.property (congrArg Subtype.val h)

/-- A proved Catalan upper bound. Equality still requires showing that
every Dyck word comes from a matching, which is not assumed here. -/
theorem noncrossing_pair_pattern_count_le_catalan (m : Nat) :
    noncrossingPairPatternCount (2 * m) ≤ catalan m := by
  classical
  have h := Fintype.card_le_of_injective (matchingDyckMap m) (matchingDyckMap_injective m)
  rw [DyckWord.card_dyckWord_semilength_eq_catalan] at h
  exact h

#print axioms matchingDyckMap_injective
#print axioms noncrossing_pair_pattern_count_le_catalan

end LC004
