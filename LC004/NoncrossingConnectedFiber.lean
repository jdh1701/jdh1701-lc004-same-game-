import LC004.NoncrossingClosureRegions

namespace LC004

theorem noncrossingClosure_eq_iff_regions_connected {n : Nat}
    (p pi : ColorPattern n) (hp : p ≤ pi) (hnc : PatternNoncrossing pi) :
    noncrossingClosure p = pi ↔ ∀ q : Quotient pi,
      NCConnected (restrictColorPattern p (patternRegionEmbed pi q)) := by
  constructor
  · intro h
    subst pi
    exact noncrossingClosure_regions_connected p
  · intro h
    apply le_antisymm (noncrossingClosure_minimal p pi hp hnc)
    intro a b hab
    obtain ⟨q,i,rfl⟩ := patternRegionEmbed_cover pi a
    obtain ⟨j,rfl⟩ := patternRegionEmbed_saturated pi pi le_rfl q i b hab
    have he := h q
    rw [NCConnected, noncrossingClosure_restrict p pi hp hnc] at he
    apply (restrictColorPattern_rel _ _ i j).mp
    rw [he]
    trivial

/-- Exact bijection between a noncrossing closure fiber and independent
connected patterns on its blocks. -/
noncomputable def connectedClosureFiberEquiv {n : Nat} (pi : ColorPattern n)
    (hnc : PatternNoncrossing pi) :
    {p : ColorPattern n // noncrossingClosure p = pi} ≃
      (∀ q : Quotient pi, {r : ColorPattern (patternQuotientFiber pi q).card // NCConnected r}) where
  toFun p q := ⟨restrictColorPattern p.val (patternRegionEmbed pi q),
    (noncrossingClosure_eq_iff_regions_connected p.val pi
      (by simpa only [p.property] using le_noncrossingClosure p.val) hnc).mp p.property q⟩
  invFun c := by
    let r := (regionPatternEquiv pi).symm (fun q => (c q).val)
    refine ⟨r.val, (noncrossingClosure_eq_iff_regions_connected r.val pi r.property hnc).mpr ?_⟩
    intro q
    have he := congrFun ((regionPatternEquiv pi).apply_symm_apply (fun q => (c q).val)) q
    change restrictColorPattern r.val (patternRegionEmbed pi q) = (c q).val at he
    rw [he]
    exact (c q).property
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun x : {p : ColorPattern n // p ≤ pi} => x.val) ((regionPatternEquiv pi).symm_apply_apply
      ⟨p.val, by simpa only [p.property] using le_noncrossingClosure p.val⟩)
  right_inv c := by
    funext q
    apply Subtype.ext
    exact congrFun ((regionPatternEquiv pi).apply_symm_apply (fun q => (c q).val)) q

#print axioms noncrossingClosure_eq_iff_regions_connected
#print axioms connectedClosureFiberEquiv
end LC004
