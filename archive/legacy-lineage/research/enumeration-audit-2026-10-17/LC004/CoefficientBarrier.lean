import LC004.CoefficientFactorization
import LC004.GrammarNormalForm

namespace LC004

/-- If cumulative values only see the meet with a barrier, coefficients
outside that barrier vanish. The invariance hypothesis is explicit. -/
theorem coefficient_zero_outside_barrier {P : Type*} [Fintype P] [Lattice P]
    (a : P → ℤ) (b : P)
    (h : ∀ x, zetaSum a x = zetaSum a (x ⊓ b))
    (p : P) (hp : ¬p ≤ b) : a p = 0 := by
  classical
  let c : P → ℤ := fun r => if r ≤ b then a r else 0
  have hz (x : P) : zetaSum c x = zetaSum a (x ⊓ b) := by
    apply Finset.sum_congr rfl
    intro r hr
    change (if r ≤ x then (if r ≤ b then a r else 0) else 0) =
      (if r ≤ x ⊓ b then a r else 0)
    rw [le_inf_iff]
    by_cases hx : r ≤ x <;> by_cases hb : r ≤ b <;> simp [hx,hb]
  have he : a = c := zetaSum_injective (fun x => (h x).trans (hz x).symm)
  have := congrFun he p
  simpa [c,hp] using this

/-- The two four-position pairing conditions intersect in four separately
solvable grammar gaps. Identifying these conditions with forced partition
witnesses is a separate geometric obligation. -/
theorem four_gap_pairing_intersection (u v w z : List Nat) :
    ((ClickGrammar u ∧ ClickGrammar w ∧ ClickGrammar (v ++ z)) ∧
     (ClickGrammar v ∧ ClickGrammar z ∧ ClickGrammar (u ++ w))) ↔
    (ClickGrammar u ∧ ClickGrammar v ∧ ClickGrammar w ∧ ClickGrammar z) := by
  constructor
  · rintro ⟨⟨hu,hw,_⟩,⟨hv,hz,_⟩⟩
    exact ⟨hu,hv,hw,hz⟩
  · rintro ⟨hu,hv,hw,hz⟩
    exact ⟨⟨hu,hw,hv.append hz⟩,⟨hv,hz,hu.append hw⟩⟩

/-- Removing the individual pairing indicators from their union leaves
minus their intersection, the sign needed for four-block cancellation. -/
theorem two_pairing_indicator (A B : Prop) [Decidable A] [Decidable B] :
    (if A ∨ B then (1 : ℤ) else 0) - (if A then 1 else 0) -
      (if B then 1 else 0) = -(if A ∧ B then 1 else 0) := by
  by_cases ha : A <;> by_cases hb : B <;> simp [ha,hb]

#print axioms coefficient_zero_outside_barrier
#print axioms four_gap_pairing_intersection
#print axioms two_pairing_indicator

end LC004
