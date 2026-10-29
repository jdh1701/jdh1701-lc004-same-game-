import LC004.NoncrossingClosure
import LC004.NoncrossingRegionPatternEquiv

namespace LC004

/-- Noncrossing local patterns glue on any disjoint noncrossing region cover.
No pair/triple size restriction is needed. -/
theorem assembledPattern_noncrossing {n : Nat} {ι : Type*} {m : ι → Nat}
    (e : ∀ k, Fin (m k) ↪o Fin n) (c : ∀ k, ColorPattern (m k))
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l)
    (noncrossing : ∀ k l i j s t,
      e k i < e l s → e l s < e k j → e k j < e l t → k = l)
    (hc : ∀ k, PatternNoncrossing (c k)) :
    PatternNoncrossing (assembledPattern e c cover disjoint) := by
  rintro a b d f hab hbd hdf ⟨k, i, j, rfl, rfl, hij⟩
    ⟨l, s, t, rfl, rfl, hst⟩
  have h := noncrossing k l i j s t hab hbd hdf
  subst l
  refine ⟨k, i, s, rfl, rfl, ?_⟩
  exact hc k i s j t ((e k).lt_iff_lt.mp hab)
    ((e k).lt_iff_lt.mp hbd) ((e k).lt_iff_lt.mp hdf) hij hst

theorem restrictColorPattern_noncrossing {n m : Nat} (p : ColorPattern n)
    (e : Fin m ↪o Fin n) (hp : PatternNoncrossing p) :
    PatternNoncrossing (restrictColorPattern p e) := by
  intro a b c d hab hbc hcd hac hbd
  apply (restrictColorPattern_rel p e a b).mpr
  exact hp (e a) (e b) (e c) (e d) (e.strictMono hab) (e.strictMono hbc)
    (e.strictMono hcd)
    ((restrictColorPattern_rel p e a c).mp hac)
    ((restrictColorPattern_rel p e b d).mp hbd)

/-- Within a noncrossing coarsening, noncrossingness is detected locally. -/
theorem noncrossing_iff_regions {n : Nat} (pi : ColorPattern n)
    (hnc : PatternNoncrossing pi) (p : {p : ColorPattern n // p ≤ pi}) :
    PatternNoncrossing p.val ↔ ∀ q, PatternNoncrossing (regionPatternEquiv pi p q) := by
  constructor
  · intro hp q
    exact restrictColorPattern_noncrossing p.val _ hp
  · intro hp
    have h := assembledPattern_noncrossing (patternRegionEmbed pi)
      (regionPatternEquiv pi p) (patternRegionEmbed_cover pi)
      (patternRegionEmbed_disjoint pi) (patternRegionEmbed_noncrossing pi hnc) hp
    change PatternNoncrossing ((regionPatternEquiv pi).symm (regionPatternEquiv pi p)).val at h
    simpa only [Equiv.symm_apply_apply] using h

/-- Closing a refinement commutes with restriction to each block of a
noncrossing coarsening. This is an equality of actual setoids. -/
theorem noncrossingClosure_restrict {n : Nat} (p pi : ColorPattern n)
    (hp : p ≤ pi) (hnc : PatternNoncrossing pi) (q : Quotient pi) :
    noncrossingClosure (restrictColorPattern p (patternRegionEmbed pi q)) =
      restrictColorPattern (noncrossingClosure p) (patternRegionEmbed pi q) := by
  classical
  let e := regionPatternOrderIso pi
  let r : {p : ColorPattern n // p ≤ pi} := ⟨p,hp⟩
  let c := fun q => noncrossingClosure (e r q)
  let a := e.symm c
  have ha : PatternNoncrossing a.val :=
    (noncrossing_iff_regions pi hnc a).mpr (by
      intro q
      change PatternNoncrossing (e (e.symm c) q)
      simpa only [OrderIso.apply_symm_apply] using noncrossingClosure_noncrossing (e r q))
  have hpa : p ≤ a.val := by
    change r ≤ a
    apply e.le_iff_le.mp
    change e r ≤ e (e.symm c)
    rw [OrderIso.apply_symm_apply]
    exact fun q => le_noncrossingClosure (e r q)
  apply le_antisymm
  · exact noncrossingClosure_minimal _ _
      (restrictColorPattern_mono (le_noncrossingClosure p) _)
      (restrictColorPattern_noncrossing _ _ (noncrossingClosure_noncrossing p))
  · have h := restrictColorPattern_mono (noncrossingClosure_minimal p a.val hpa ha)
      (patternRegionEmbed pi q)
    have he : restrictColorPattern a.val (patternRegionEmbed pi q) = c q :=
      congrFun (e.apply_symm_apply c) q
    rw [he] at h
    exact h

/-- Every block of the noncrossing closure contains a connected local pattern. -/
theorem noncrossingClosure_regions_connected {n : Nat} (p : ColorPattern n)
    (q : Quotient (noncrossingClosure p)) :
    NCConnected (restrictColorPattern p (patternRegionEmbed (noncrossingClosure p) q)) := by
  rw [NCConnected, noncrossingClosure_restrict p (noncrossingClosure p)
    (le_noncrossingClosure p) (noncrossingClosure_noncrossing p)]
  apply Setoid.ext
  intro i j
  rw [restrictColorPattern_rel]
  change noncrossingClosure p _ _ ↔ True
  exact ⟨fun _ => trivial, fun _ => Quotient.exact
    ((patternRegionEmbed_class _ q i).trans (patternRegionEmbed_class _ q j).symm)⟩

#print axioms assembledPattern_noncrossing
#print axioms noncrossingClosure_restrict
#print axioms noncrossingClosure_regions_connected
end LC004
