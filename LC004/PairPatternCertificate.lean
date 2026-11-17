import LC004.MatchingMergeProfile

namespace LC004

@[simp] theorem mem_patternQuotientFiber {n : Nat} (p : ColorPattern n)
    (q : Quotient p) (i : Fin n) :
    i ∈ patternQuotientFiber p q ↔ Quotient.mk p i = q := by
  classical
  simp [patternQuotientFiber]

/-- Enumerate each equivalence class once and enumerate each of its
positions once. The arbitrary enumeration order has no counting role. -/
noncomputable def patternBlockLists {n : Nat} (p : ColorPattern n) :
    List (List (Fin n)) := by
  classical
  exact (Finset.univ : Finset (Quotient p)).toList.map
    (fun q => (patternQuotientFiber p q).toList)

theorem patternBlockLists_flatten_nodup {n : Nat} (p : ColorPattern n) :
    (patternBlockLists p).flatten.Nodup := by
  classical
  apply List.nodup_flatten.mpr
  constructor
  · intro b hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    exact Finset.nodup_toList _
  · apply List.pairwise_map.mpr
    apply (Finset.nodup_toList (Finset.univ : Finset (Quotient p))).imp
    intro q r hne
    rw [List.disjoint_left]
    intro i hi hr
    have hq : Quotient.mk p i = q := by simpa using hi
    have hr' : Quotient.mk p i = r := by simpa using hr
    exact hne (hq.symm.trans hr')

theorem patternBlockLists_exact_cover {n : Nat} (p : ColorPattern n) :
    (patternBlockLists p).flatten.Perm (List.finRange n) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (patternBlockLists_flatten_nodup p) (List.nodup_finRange n)
  ext i
  have hi : i ∈ (patternBlockLists p).flatten := by
    apply List.mem_flatten.mpr
    refine ⟨(patternQuotientFiber p (Quotient.mk p i)).toList, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨Quotient.mk p i, by simp, rfl⟩
    · simp
  simp only [List.mem_toFinset, List.mem_finRange, iff_true]
  exact hi

/-- The ordered-endpoint matching condition rules out every crossing
witness between class blocks, including a block paired with itself. -/
theorem pair_pattern_fibers_no_cross {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (q r : Quotient p) :
    ¬ BlocksCross ((patternQuotientFiber p q).toList.map Fin.val)
      ((patternQuotientFiber p r).toList.map Fin.val) := by
  classical
  rintro ⟨u, hu, v, hv, s, hs, t, ht, hcross⟩
  obtain ⟨iu, hiu, heu⟩ := List.mem_map.mp hu
  obtain ⟨iv, hiv, hev⟩ := List.mem_map.mp hv
  obtain ⟨is, his, hes⟩ := List.mem_map.mp hs
  obtain ⟨it, hit, het⟩ := List.mem_map.mp ht
  have huq : Quotient.mk p iu = q := by simpa using hiu
  have hvq : Quotient.mk p iv = q := by simpa using hiv
  have hsr : Quotient.mk p is = r := by simpa using his
  have htr : Quotient.mk p it = r := by simpa using hit
  have huv : p iu iv := Quotient.exact (huq.trans hvq.symm)
  have hst : p is it := Quotient.exact (hsr.trans htr.symm)
  have hc : PairCross iu.val iv.val is.val it.val := by
    simpa only [heu, hev, hes, het] using hcross
  rcases hc with ⟨hus, hsv, hvt⟩ | ⟨hsu, hut, htv⟩
  · exact hp.2 iu is iv it hus hsv hvt ⟨huv, hst⟩
  · exact hp.2 is iu it iv hsu hut htv ⟨hst, huv⟩

/-- A perfect noncrossing matching gives a complete monochromatic
certificate for its unlabeled color pattern. No enumeration theorem
or prior assumption of winning is used in this construction. -/
noncomputable def pairPatternCertificate {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) :
    Noncrossing23Certificate (patternColor p) where
  blocks := patternBlockLists p
  sizes := by
    intro b hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    left
    rw [Finset.length_toList]
    exact pair_pattern_quotient_fiber_card p hp q
  exactCover := patternBlockLists_exact_cover p
  monochromatic := by
    intro b hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    refine ⟨q.out, ?_⟩
    intro i hi
    have hq : Quotient.mk p i = q := by simpa using hi
    exact congrArg Quotient.out hq
  noncrossing := by
    intro xs hxs ys hys
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hys
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    exact pair_pattern_fibers_no_cross p hp q r

theorem noncrossing_pair_pattern_winning {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) : WinningColorPattern p :=
  ⟨pairPatternCertificate p hp⟩

/-- Every element of the actual matching representation space maps to
a genuine winning pattern, in addition to the proved fourfold profile. -/
theorem fourfold_representation_winning {n : Nat}
    (r : FourfoldMatchingRepresentation n) :
    WinningColorPattern (fourfoldRepresentationPattern r) :=
  winning_mergePatternClasses r.1.val r.2.val
    (noncrossing_pair_pattern_winning r.1.val r.1.property)

/-- The global representation map now has a winning-pattern codomain.
Its surjectivity and exact fibers remain separate obligations. -/
def fourfoldRepresentationWinningMap {n : Nat}
    (r : FourfoldMatchingRepresentation n) :
    {p : ColorPattern n // WinningColorPattern p} :=
  ⟨fourfoldRepresentationPattern r, fourfold_representation_winning r⟩

/-- For a pair-colored pattern, a certificate block containing i is
forced to equal i's entire color class: it has at least two positions
and is contained in a class of exactly two positions. -/
theorem certificate_block_eq_pair_class {n : Nat} (p : ColorPattern n)
    (hpair : ∀ i : Fin n, Nat.card {j : Fin n // p i j} = 2)
    (cert : Noncrossing23Certificate (patternColor p))
    {b : List (Fin n)} (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b) :
    b.toFinset = patternClassPositions p i := by
  classical
  obtain ⟨a, ha⟩ := cert.monochromatic b hb
  have hsub : b.toFinset ⊆ patternClassPositions p i := by
    intro j hj
    have hjb := List.mem_toFinset.mp hj
    have hij : p i j := (patternColor_eq_iff p i j).mp
      ((ha i hi).trans (ha j hjb).symm)
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using hij
  have hclass : (patternClassPositions p i).card = 2 := by
    simpa only [patternClassPositions, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using hpair i
  have hnodup := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  have hlen := cert.sizes b hb
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hclass, List.toFinset_card_of_nodup hnodup]
  rcases hlen with hlen | hlen <;> omega

theorem winning_pair_pattern_iff {n : Nat} (p : ColorPattern n)
    (hpair : ∀ i : Fin n, Nat.card {j : Fin n // p i j} = 2) :
    WinningColorPattern p ↔ NoncrossingPairPattern p := by
  constructor
  · rintro ⟨cert⟩
    refine ⟨hpair, ?_⟩
    intro a b c d hab hbc hcd hcross
    obtain ⟨ablock, ha, hap⟩ := cert.cover_position a
    obtain ⟨bblock, hb, hbp⟩ := cert.cover_position b
    have hac := certificate_block_eq_pair_class p hpair cert ha hap
    have hbd := certificate_block_eq_pair_class p hpair cert hb hbp
    have hc : c ∈ ablock := by
      apply List.mem_toFinset.mp
      rw [hac]
      simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using hcross.1
    have hd : d ∈ bblock := by
      apply List.mem_toFinset.mp
      rw [hbd]
      simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using hcross.2
    exact cert.no_alternation ha hb hap hc hbp hd (Or.inl ⟨hab, hbc, hcd⟩)
  · exact noncrossing_pair_pattern_winning p

/-- Winning patterns with every color used twice are exactly the
noncrossing perfect matchings, as finite unlabeled object spaces. -/
def pairWinningPatternEquiv (n : Nat) :
    {p : ColorPattern n // NoncrossingPairPattern p} ≃
    {p : ColorPattern n // WinningColorPattern p ∧
      ∀ i : Fin n, Nat.card {j : Fin n // p i j} = 2} where
  toFun p := ⟨p.val, noncrossing_pair_pattern_winning p.val p.property, p.property.1⟩
  invFun p := ⟨p.val, (winning_pair_pattern_iff p.val p.property.2).mp p.property.1⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

#print axioms winning_pair_pattern_iff
#print axioms pairWinningPatternEquiv
#print axioms patternBlockLists_exact_cover
#print axioms noncrossing_pair_pattern_winning
#print axioms fourfold_representation_winning

end LC004
