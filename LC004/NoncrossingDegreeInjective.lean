import LC004.NoncrossingLastBlock

namespace LC004

/-- At the first differing class assignment, an older proposed class
would cross a later unfinished class. Equal opening sizes force that
later class to have a member beyond the first disagreement. -/
theorem noncrossing_leader_not_lt {n : Nat} (p t : ColorPattern n)
    (hp : PatternNoncrossing p)
    (hdegree : ∀ j, patternOpeningDegree p j = patternOpeningDegree t j)
    (i : Fin n)
    (hprefix : ∀ j, j < i → patternClassLeader p j = patternClassLeader t j) :
    ¬ patternClassLeader p i < patternClassLeader t i := by
  classical
  intro hab
  let a := patternClassLeader p i
  let b := patternClassLeader t i
  have hta : patternClassLeader p a = a := patternClassLeader_idempotent p i
  have htb : patternClassLeader t b = b := patternClassLeader_idempotent t i
  have hpbb : patternClassLeader p b = b := by
    apply (opening_degree_pos_iff_leader p b).mp
    rw [hdegree b]
    exact (opening_degree_pos_iff_leader t b).mpr htb
  have hbi : b < i := by
    have hle := patternClassLeader_le t i
    apply lt_of_le_of_ne hle
    intro heq
    have hti : patternClassLeader t i = i := heq
    have hpi : patternClassLeader p i = i := by
      apply (opening_degree_pos_iff_leader p i).mp
      rw [hdegree i]
      exact (opening_degree_pos_iff_leader t i).mpr hti
    change patternClassLeader p i < patternClassLeader t i at hab
    rw [hti, hpi] at hab
    exact (lt_irrefl i) hab
  have hsize : (patternClassPositions p b).card = (patternClassPositions t b).card := by
    have h := hdegree b
    rw [patternOpeningDegree_eq, patternOpeningDegree_eq] at h
    change (if patternClassLeader p b = b then _ else 0) =
      (if patternClassLeader t b = b then _ else 0) at h
    simpa only [hpbb, htb, if_pos rfl] using h
  have hiT : i ∈ patternClassPositions t b := by
    have h := patternClassLeader_related t i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hiP : i ∉ patternClassPositions p b := by
    intro h
    have hrel := (Finset.mem_filter.mp h).2
    have he := (pattern_related_iff_leaders p b i).mp hrel
    rw [hpbb] at he
    exact (ne_of_lt hab) he.symm
  have hnot : ¬ patternClassPositions p b ⊆ patternClassPositions t b := by
    intro hsub
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hsize.symm)
    exact hiP (heq.symm ▸ hiT)
  obtain ⟨j, hjP, hjT⟩ := Finset.not_subset.mp hnot
  have hij : i < j := by
    by_contra h
    have hle : j ≤ i := le_of_not_gt h
    have hne : j ≠ i := by
      intro heq
      exact hiP (heq ▸ hjP)
    have hji : j < i := lt_of_le_of_ne hle hne
    have hrel := (Finset.mem_filter.mp hjP).2
    have he := (pattern_related_iff_leaders p b j).mp hrel
    rw [hpbb, hprefix j hji] at he
    have htj : t b j := (pattern_related_iff_leaders t b j).mpr (htb.trans he)
    exact hjT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htj⟩)
  have hai : p a i := patternClassLeader_related p i
  have hbj : p b j := (Finset.mem_filter.mp hjP).2
  have hcross := hp a b i j hab hbi hij hai hbj
  have he := (pattern_related_iff_leaders p a b).mp hcross
  rw [hta, hpbb] at he
  exact (ne_of_lt hab) he

/-- Conventional noncrossing partitions are determined by class sizes
at their first positions. No restriction on block sizes is required. -/
theorem noncrossing_pattern_eq_of_opening_degree {n : Nat} (p t : ColorPattern n)
    (hp : PatternNoncrossing p) (ht : PatternNoncrossing t)
    (hdegree : ∀ j, patternOpeningDegree p j = patternOpeningDegree t j) : p = t := by
  have aux : ∀ k : Nat, ∀ i : Fin n, i.val = k →
      patternClassLeader p i = patternClassLeader t i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      have hpre : ∀ j, j < i → patternClassLeader p j = patternClassLeader t j := by
        intro j hj
        apply ih j.val (by change j.val < i.val at hj; omega) j rfl
      apply le_antisymm
      · exact le_of_not_gt (noncrossing_leader_not_lt t p ht
          (fun j => (hdegree j).symm) i (fun j hj => (hpre j hj).symm))
      · exact le_of_not_gt (noncrossing_leader_not_lt p t hp hdegree i hpre)
  apply Setoid.ext
  intro i j
  rw [pattern_related_iff_leaders p, pattern_related_iff_leaders t,
    aux i.val i rfl, aux j.val j rfl]

theorem noncrossing_tree_degrees_injective (n : Nat) :
    Function.Injective (fun p : {p : ColorPattern n // PatternNoncrossing p} =>
      patternTreeDegrees p.val) := by
  intro p t h
  have hlist : List.ofFn (patternOpeningDegree p.val) =
      List.ofFn (patternOpeningDegree t.val) := List.append_cancel_right h
  have hfun := List.ofFn_injective hlist
  apply Subtype.ext
  exact noncrossing_pattern_eq_of_opening_degree p.val t.val p.property t.property
    (fun i => congrFun hfun i)

#print axioms noncrossing_pattern_eq_of_opening_degree
#print axioms noncrossing_tree_degrees_injective

end LC004
