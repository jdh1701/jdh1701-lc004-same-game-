import LC004.FourGapRefinementIndicator
import LC004.CollectedJoinCoefficients

namespace LC004
open scoped BigOperators Classical

noncomputable def pairCut {n : Nat} (c d : Fin n) : ColorPattern n :=
  Setoid.ker (fun x => decide (x = c ∨ x = d))

theorem lowerIncidence_sub {α : Type*} [Fintype α] [PartialOrder α]
    (f g : α → Int) (r : α) :
    lowerIncidence (fun q => f q - g q) r = lowerIncidence f r - lowerIncidence g r := by
  classical
  unfold lowerIncidence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : q ≤ r <;> simp [h]

noncomputable def fourOverlapCoefficient {n : Nat} (b c d : Fin n)
    (p : ColorPattern n) : Int :=
  winningJoinCoefficient n p -
    (if p ≤ pairCut c d then winningJoinCoefficient n p else 0) -
    (if p ≤ pairCut b c then winningJoinCoefficient n p else 0)

theorem fourOverlapCoefficient_incidence {n : Nat} (b c d : Fin n)
    (r : ColorPattern n) :
    lowerIncidence (fourOverlapCoefficient b c d) r =
      (if WinningColorPattern r then (1 : Int) else 0) -
      (if WinningColorPattern (splitOffPair r c d) then 1 else 0) -
      (if WinningColorPattern (splitOffPair r b c) then 1 else 0) := by
  unfold fourOverlapCoefficient
  rw [lowerIncidence_sub,lowerIncidence_sub,
    lowerIncidence_truncate,lowerIncidence_truncate]
  simp only [winningJoinCoefficient_incidence,splitOffPair,pairCut]

theorem restrict_meet_eq_of_homogeneous {n m : Nat} (r rho : ColorPattern n)
    (e : Fin m → Fin n) (h : ∀ i j, rho (e i) (e j)) :
    restrictColorPattern (r ⊓ rho) e = restrictColorPattern r e := by
  apply Setoid.ext
  intro i j
  simp only [restrictColorPattern_rel]
  exact and_iff_left (h i j)

theorem fourGapsWin_meet_iff {n : Nat} (r rho : ColorPattern n) (a b c d : Fin n)
    (hgap : ∀ S ∈ [pairInterior a b,pairInterior b c,pairInterior c d,pairExterior a d],
      ∀ x ∈ S, ∀ y ∈ S, rho x y) :
    FourGapsWin (r ⊓ rho) a b c d ↔ FourGapsWin r a b c d := by
  have he (S : Finset (Fin n))
      (hS : S ∈ [pairInterior a b,pairInterior b c,pairInterior c d,pairExterior a d]) :
      restrictColorPattern (r ⊓ rho) (S.orderEmbOfFin rfl) =
        restrictColorPattern r (S.orderEmbOfFin rfl) :=
    restrict_meet_eq_of_homogeneous r rho _
      (fun i j => hgap S hS _ (S.orderEmbOfFin_mem rfl i) _ (S.orderEmbOfFin_mem rfl j))
  unfold FourGapsWin
  rw [he _ (by simp),he _ (by simp),he _ (by simp),he _ (by simp)]

/-- Cancellation is forced when a gap-homogeneous partition separates the
target. The assumptions concern only explicit equality relations, not coefficients. -/
theorem winningJoinCoefficient_zero_of_four_gap_separator {n : Nat}
    (p rho : ColorPattern n) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d})
    (hrab : rho a b) (hrac : rho a c) (hrad : rho a d)
    (hgap : ∀ S ∈ [pairInterior a b,pairInterior b c,pairInterior c d,pairExterior a d],
      ∀ x ∈ S, ∀ y ∈ S, rho x y)
    (hsep : ¬ p ≤ rho) : winningJoinCoefficient n p = 0 := by
  have hi (r : ColorPattern n) (hrp : r ≤ p) :
      lowerIncidence (fourOverlapCoefficient b c d) r =
      -(if r a b ∧ r a c ∧ r a d ∧ FourGapsWin r a b c d then 1 else 0) := by
    rw [fourOverlapCoefficient_incidence]
    exact four_gap_indicator_below p r hrp hab hbc hcd hclass
  have inv (r : ColorPattern n) (hrp : r ≤ p) :
      lowerIncidence (fourOverlapCoefficient b c d) r =
      lowerIncidence (fourOverlapCoefficient b c d) (r ⊓ rho) := by
    rw [hi r hrp,hi (r ⊓ rho) (le_trans inf_le_left hrp)]
    have he : ((r ⊓ rho) a b ∧ (r ⊓ rho) a c ∧ (r ⊓ rho) a d ∧
        FourGapsWin (r ⊓ rho) a b c d) ↔
        (r a b ∧ r a c ∧ r a d ∧ FourGapsWin r a b c d) := by
      change ((r a b ∧ rho a b) ∧ (r a c ∧ rho a c) ∧ (r a d ∧ rho a d) ∧ _) ↔ _
      simp only [hrab,hrac,hrad,and_true,fourGapsWin_meet_iff r rho a b c d hgap]
    simp only [he]
  have hz := incidence_support_of_local_meet_invariance
    (fourOverlapCoefficient b c d) rho p inv hsep
  have hpa (x : Fin n) (hx : x ∈ ({a,b,c,d} : Finset (Fin n))) : p a x := by
    have : x ∈ patternClassPositions p a := hclass.symm ▸ hx
    simpa [patternClassPositions] using this
  have hcut1 : ¬ p ≤ pairCut c d := by
    intro h
    have he : decide (a = c ∨ a = d) = decide (c = c ∨ c = d) := h (hpa c (by simp))
    have hac : a ≠ c := by omega
    have had : a ≠ d := by omega
    simp [hac,had] at he
  have hcut2 : ¬ p ≤ pairCut b c := by
    intro h
    have he : decide (a = b ∨ a = c) = decide (b = b ∨ b = c) := h (hpa b (by simp))
    have hab' : a ≠ b := by omega
    have hac : a ≠ c := by omega
    simp [hab',hac] at he
  simpa [fourOverlapCoefficient,hcut1,hcut2] using hz

#print axioms fourOverlapCoefficient_incidence
#print axioms winningJoinCoefficient_zero_of_four_gap_separator
end LC004
