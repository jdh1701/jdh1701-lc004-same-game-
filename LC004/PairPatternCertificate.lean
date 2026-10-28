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
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht
  have huq : Quotient.mk p u = q := by simpa using hu
  have hvq : Quotient.mk p v = q := by simpa using hv
  have hsr : Quotient.mk p s = r := by simpa using hs
  have htr : Quotient.mk p t = r := by simpa using ht
  have huv : p u v := Quotient.exact (huq.trans hvq.symm)
  have hst : p s t := Quotient.exact (hsr.trans htr.symm)
  rcases hcross with ⟨hus, hsv, hvt⟩ | ⟨hsu, hut, htv⟩
  · exact hp.2 u s v t hus hsv hvt ⟨huv, hst⟩
  · exact hp.2 s u t v hsu hut htv ⟨hst, huv⟩

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

#print axioms patternBlockLists_exact_cover
#print axioms noncrossing_pair_pattern_winning
#print axioms fourfold_representation_winning

end LC004
