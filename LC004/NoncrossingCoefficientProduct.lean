import LC004.NoncrossingRegionPatternEquiv
import LC004.ProductIncidence
import LC004.CollectedJoinCoefficients
import LC004.NoncrossingClosure

namespace LC004
open scoped BigOperators Classical

theorem prod_prop_indicator {ι : Type*} [Fintype ι] (P : ι → Prop) :
    (∏ i, if P i then (1 : Int) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Collected signed game coefficients, rather than certificates, factor
over the blocks of every noncrossing coarsening. -/
theorem winningJoinCoefficient_noncrossing_product {n : Nat}
    (p pi : ColorPattern n) (hp : p ≤ pi) (hnc : PatternNoncrossing pi) :
    winningJoinCoefficient n p =
      ∏ q : Quotient pi,
        winningJoinCoefficient (patternQuotientFiber pi q).card
          (restrictColorPattern p (patternRegionEmbed pi q)) := by
  classical
  let e := regionPatternOrderIso pi
  let c : (∀ q : Quotient pi, ColorPattern (patternQuotientFiber pi q).card) → Int := fun fs => ∏ q : Quotient pi,
    winningJoinCoefficient (patternQuotientFiber pi q).card (fs q)
  have hc (r : {r : ColorPattern n // r ≤ pi}) :
      lowerIncidence (fun s => c (e s)) r =
        if WinningColorPattern r.val then 1 else 0 := by
    rw [lowerIncidence_orderIso]
    change lowerIncidence (fun fs : (∀ q : Quotient pi, ColorPattern (patternQuotientFiber pi q).card) => ∏ q : Quotient pi,
      winningJoinCoefficient (patternQuotientFiber pi q).card (fs q)) (e r) = _
    have hprod : lowerIncidence (fun fs : (∀ q : Quotient pi, ColorPattern (patternQuotientFiber pi q).card) => ∏ q : Quotient pi,
        winningJoinCoefficient (patternQuotientFiber pi q).card (fs q)) (e r) =
        ∏ q : Quotient pi, lowerIncidence
          (winningJoinCoefficient (patternQuotientFiber pi q).card) ((e r) q) :=
      lowerIncidence_pi_product
        (fun q : Quotient pi => winningJoinCoefficient (patternQuotientFiber pi q).card) (e r)
    rw [hprod]
    simp_rw [winningJoinCoefficient_incidence]
    rw [prod_prop_indicator]
    have he : (∀ q : Quotient pi,
        WinningColorPattern ((e r) q)) ↔ WinningColorPattern r.val :=
      (winning_iff_noncrossing_coarsening_regions r.val pi r.property hnc).symm
    simp only [he]
  have he : (fun r : {r : ColorPattern n // r ≤ pi} => winningJoinCoefficient n r.val) =
      (fun r => c (e r)) := by
    apply lowerIncidence_injective
    funext r
    rw [lowerIncidence_Iic,winningJoinCoefficient_incidence]
    exact (hc r).symm
  exact congrFun he ⟨p,hp⟩

#print axioms winningJoinCoefficient_noncrossing_product

theorem winningJoinCoefficient_closure_components {n : Nat} (p : ColorPattern n) :
    winningJoinCoefficient n p =
      ∏ q : Quotient (noncrossingClosure p),
        winningJoinCoefficient (patternQuotientFiber (noncrossingClosure p) q).card
          (restrictColorPattern p (patternRegionEmbed (noncrossingClosure p) q)) :=
  winningJoinCoefficient_noncrossing_product p (noncrossingClosure p)
    (le_noncrossingClosure p) (noncrossingClosure_noncrossing p)

#print axioms winningJoinCoefficient_closure_components
end LC004
