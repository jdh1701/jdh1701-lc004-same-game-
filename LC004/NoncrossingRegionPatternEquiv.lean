import LC004.NoncrossingRegionEquivalence

namespace LC004
open scoped Classical

noncomputable def patternRegionEmbed {n : Nat} (pi : ColorPattern n) (q : Quotient pi) :=
  (patternQuotientFiber pi q).orderEmbOfFin rfl

theorem patternRegionEmbed_class {n : Nat} (pi : ColorPattern n) (q : Quotient pi)
    (i : Fin (patternQuotientFiber pi q).card) : Quotient.mk pi (patternRegionEmbed pi q i) = q :=
  (mem_patternQuotientFiber pi q _).mp ((patternQuotientFiber pi q).orderEmbOfFin_mem rfl i)

theorem patternRegionEmbed_cover {n : Nat} (pi : ColorPattern n) (a : Fin n) :
    ∃ q i, patternRegionEmbed pi q i = a := by
  refine ⟨Quotient.mk pi a, ?_⟩
  have hm : a ∈ patternQuotientFiber pi (Quotient.mk pi a) := by simp
  change a ∈ Set.range ((patternQuotientFiber pi (Quotient.mk pi a)).orderEmbOfFin rfl)
  simpa only [Finset.range_orderEmbOfFin] using hm

theorem patternRegionEmbed_disjoint {n : Nat} (pi : ColorPattern n)
    (q r : Quotient pi) (i j) (h : patternRegionEmbed pi q i = patternRegionEmbed pi r j) : q = r := by
  rw [← patternRegionEmbed_class pi q i,← patternRegionEmbed_class pi r j,h]

theorem patternRegionEmbed_saturated {n : Nat} (p pi : ColorPattern n) (hp : p ≤ pi)
    (q : Quotient pi) (i) (b : Fin n) (h : p (patternRegionEmbed pi q i) b) :
    ∃ j, patternRegionEmbed pi q j = b := by
  have he : Quotient.mk pi b = q :=
    (Quotient.sound (pi.symm (hp h))).trans (patternRegionEmbed_class pi q i)
  have hm : b ∈ patternQuotientFiber pi q := (mem_patternQuotientFiber pi q b).mpr he
  change b ∈ Set.range ((patternQuotientFiber pi q).orderEmbOfFin rfl)
  simpa only [Finset.range_orderEmbOfFin] using hm

theorem patternRegionEmbed_noncrossing {n : Nat} (pi : ColorPattern n)
    (hnc : PatternNoncrossing pi) (q r : Quotient pi) (i j s t)
    (h1 : patternRegionEmbed pi q i < patternRegionEmbed pi r s)
    (h2 : patternRegionEmbed pi r s < patternRegionEmbed pi q j)
    (h3 : patternRegionEmbed pi q j < patternRegionEmbed pi r t) : q = r := by
  have hq : pi (patternRegionEmbed pi q i) (patternRegionEmbed pi q j) :=
    Quotient.exact ((patternRegionEmbed_class pi q i).trans (patternRegionEmbed_class pi q j).symm)
  have hr : pi (patternRegionEmbed pi r s) (patternRegionEmbed pi r t) :=
    Quotient.exact ((patternRegionEmbed_class pi r s).trans (patternRegionEmbed_class pi r t).symm)
  have h := hnc _ _ _ _ h1 h2 h3 hq hr
  exact (patternRegionEmbed_class pi q i).symm.trans
    ((Quotient.sound h).trans (patternRegionEmbed_class pi r s))

/-- Winning factors over the actual blocks of every noncrossing coarsening. -/
theorem winning_iff_noncrossing_coarsening_regions {n : Nat} (p pi : ColorPattern n)
    (hp : p ≤ pi) (hnc : PatternNoncrossing pi) :
    WinningColorPattern p ↔ ∀ q : Quotient pi,
      WinningColorPattern (restrictColorPattern p (patternRegionEmbed pi q)) := by
  exact winning_iff_noncrossing_region_cover p _ (patternRegionEmbed pi)
    (patternRegionEmbed_cover pi) (patternRegionEmbed_disjoint pi)
    (patternRegionEmbed_noncrossing pi hnc) (patternRegionEmbed_saturated p pi hp)

/-- All refinements of a partition are canonically the product of the
partition spaces on its blocks. This counts equality patterns, not witnesses. -/
noncomputable def regionPatternEquiv {n : Nat} (pi : ColorPattern n) :
    {p : ColorPattern n // p ≤ pi} ≃
      (∀ q : Quotient pi, ColorPattern (patternQuotientFiber pi q).card) where
  toFun p q := restrictColorPattern p.val (patternRegionEmbed pi q)
  invFun c := ⟨assembledPattern (patternRegionEmbed pi) c
    (patternRegionEmbed_cover pi) (patternRegionEmbed_disjoint pi), by
      rintro a b ⟨q,i,j,rfl,rfl,_⟩
      exact Quotient.exact ((patternRegionEmbed_class pi q i).trans
        (patternRegionEmbed_class pi q j).symm)⟩
  left_inv p := by
    apply Subtype.ext
    apply le_antisymm
    · rintro a b ⟨q,i,j,rfl,rfl,h⟩
      exact (restrictColorPattern_rel p.val (patternRegionEmbed pi q) i j).mp h
    · intro a b h
      obtain ⟨q,i,rfl⟩ := patternRegionEmbed_cover pi a
      obtain ⟨j,rfl⟩ := patternRegionEmbed_saturated p.val pi p.property q i b h
      exact ⟨q,i,j,rfl,rfl,(restrictColorPattern_rel p.val (patternRegionEmbed pi q) i j).mpr h⟩
  right_inv c := by
    funext q
    apply Setoid.ext
    intro i j
    exact (restrictColorPattern_rel _ (patternRegionEmbed pi q) i j).trans
      (assembledPattern_local (patternRegionEmbed pi) c
        (patternRegionEmbed_cover pi) (patternRegionEmbed_disjoint pi) q i j)

/-- The equivalence also preserves and reflects the refinement order. -/
theorem regionPatternEquiv_le_iff {n : Nat} (pi : ColorPattern n)
    (p r : {p : ColorPattern n // p ≤ pi}) :
    regionPatternEquiv pi p ≤ regionPatternEquiv pi r ↔ p ≤ r := by
  constructor
  · intro h a b hab
    obtain ⟨q,i,rfl⟩ := patternRegionEmbed_cover pi a
    obtain ⟨j,rfl⟩ := patternRegionEmbed_saturated p.val pi p.property q i b hab
    exact (restrictColorPattern_rel r.val (patternRegionEmbed pi q) i j).mp
      (h q ((restrictColorPattern_rel p.val (patternRegionEmbed pi q) i j).mpr hab))
  · intro h q
    exact restrictColorPattern_mono h _

#print axioms winning_iff_noncrossing_coarsening_regions
#print axioms regionPatternEquiv
#print axioms regionPatternEquiv_le_iff

noncomputable def regionPatternOrderIso {n : Nat} (pi : ColorPattern n) :
    {p : ColorPattern n // p ≤ pi} ≃o
      (∀ q : Quotient pi, ColorPattern (patternQuotientFiber pi q).card) where
  toEquiv := regionPatternEquiv pi
  map_rel_iff' := regionPatternEquiv_le_iff pi _ _

#print axioms regionPatternOrderIso
end LC004
