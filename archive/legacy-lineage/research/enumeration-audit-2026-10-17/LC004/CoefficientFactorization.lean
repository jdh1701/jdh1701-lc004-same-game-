import LC004.SignedConstraints
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace LC004

noncomputable def zetaSum {P : Type*} [Fintype P] [LE P]
    (a : P → ℤ) (x : P) : ℤ := by
  classical
  exact ∑ y, if y ≤ x then a y else 0

/-- Cumulative lower-ideal sums uniquely determine coefficients on a finite poset. -/
theorem zetaSum_injective {P : Type*} [Fintype P] [PartialOrder P]
    {a b : P → ℤ} (hab : ∀ x, zetaSum a x = zetaSum b x) : a = b := by
  classical
  funext x
  have wf : WellFounded ((· < ·) : P → P → Prop) := wellFounded_lt
  induction x using wf.induction with
  | h x ih =>
    have hd : (∑ y, if y ≤ x then a y - b y else 0) = 0 := by
      have he : (∑ y, if y ≤ x then a y - b y else 0) =
          zetaSum a x - zetaSum b x := by
        simp only [zetaSum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        split_ifs <;> simp
      rw [he, hab x, sub_self]
    have he : (∑ y, if y ≤ x then a y - b y else 0) = a x - b x := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro y hy hne
        by_cases hle : y ≤ x
        · simp [hle, ih y (lt_of_le_of_ne hle hne)]
        · simp [hle]
      · simp
    exact sub_eq_zero.mp (he.symm.trans hd)

/-- Lower-ideal sums of product coefficients separate on product posets. -/
theorem zetaSum_product {P Q : Type*} [Fintype P] [Fintype Q]
    [PartialOrder P] [PartialOrder Q] (a : P → ℤ) (b : Q → ℤ) (x : P) (y : Q) :
    zetaSum (fun t : P × Q => a t.1 * b t.2) (x,y) =
      zetaSum a x * zetaSum b y := by
  classical
  simp only [zetaSum, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  change (if p ≤ x ∧ q ≤ y then a p * b q else 0) = _
  by_cases hpx : p ≤ x <;> by_cases hqy : q ≤ y <;> simp [hpx, hqy]

/-- Factorization of cumulative values forces factorization of coefficients.
The cumulative-factorization hypothesis must be proved for the application. -/
theorem coefficient_factorization {P Q : Type*} [Fintype P] [Fintype Q]
    [PartialOrder P] [PartialOrder Q]
    (a : P → ℤ) (b : Q → ℤ) (c : P × Q → ℤ)
    (h : ∀ x y, zetaSum c (x,y) = zetaSum a x * zetaSum b y) :
    ∀ x y, c (x,y) = a x * b y := by
  have he : c = fun t : P × Q => a t.1 * b t.2 := by
    apply zetaSum_injective
    intro t
    rw [zetaSum_product, h]
  intro x y
  exact congrFun he (x,y)

/-- Collect all signed terms with the same key. -/
noncomputable def collectedCoeff {P : Type*} (ts : SignedTerms P) (p : P) : ℤ := by
  classical
  exact (ts.map fun t => if t.2 = p then t.1 else 0).sum

theorem zetaSum_collectedCoeff {P : Type*} [Fintype P] [PartialOrder P]
    (ts : SignedTerms P) (x : P) :
    zetaSum (collectedCoeff ts) x = @signedEval P P (· ≤ ·) (Classical.decRel _) ts x := by
  classical
  induction ts with
  | nil => simp [zetaSum, collectedCoeff, signedEval]
  | cons t ts ih =>
    have he : collectedCoeff (t :: ts) =
        fun p => (if t.2 = p then t.1 else 0) + collectedCoeff ts p := by
      funext p
      simp [collectedCoeff]
    rw [he]
    have hz : zetaSum (fun p => (if t.2 = p then t.1 else 0) + collectedCoeff ts p) x =
        (if t.2 ≤ x then t.1 else 0) + zetaSum (collectedCoeff ts) x := by
      simp only [zetaSum]
      have hd (p : P) :
          (if p ≤ x then (if t.2 = p then t.1 else 0) + collectedCoeff ts p else 0) =
          (if p ≤ x then (if t.2 = p then t.1 else 0) else 0) +
          (if p ≤ x then collectedCoeff ts p else 0) := by
        by_cases hp : p ≤ x <;> simp [hp]
      simp_rw [hd]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single t.2]
      · simp
      · intro p hp hne
        simp [Ne.symm hne]
      · simp
    rw [hz, ih]
    simp [signedEval]

theorem collected_union_zeta {P : Type*} [Fintype P] [SemilatticeSup P]
    (ps : List P) (x : P) :
    zetaSum (collectedCoeff (unionTerms (· ⊔ ·) ps)) x =
      @ite ℤ (∃ p ∈ ps, p ≤ x) (Classical.propDecidable _) 1 0 := by
  classical
  rw [zetaSum_collectedCoeff]
  have h := signedEval_unionTerms (· ≤ ·) (· ⊔ ·) (fun _ _ _ => sup_le_iff) ps x
  by_cases hx : ∃ p ∈ ps, p ≤ x <;> simpa only [hx, if_true, if_false] using h

/-- Unconditional coefficient factorization for Cartesian-product witness lists.
Applying this to noncrossing components still requires the geometric restriction
and reconstruction theorem; no such game-specific assumption is hidden here. -/
theorem collected_union_product {P Q : Type*} [Fintype P] [Fintype Q]
    [SemilatticeSup P] [SemilatticeSup Q] (ps : List P) (qs : List Q) (x : P) (y : Q) :
    collectedCoeff (unionTerms (· ⊔ ·) (ps.flatMap fun p => qs.map fun q => (p,q))) (x,y) =
      collectedCoeff (unionTerms (· ⊔ ·) ps) x *
      collectedCoeff (unionTerms (· ⊔ ·) qs) y := by
  classical
  apply coefficient_factorization
  intro u v
  simp only [collected_union_zeta]
  have he : (∃ t ∈ ps.flatMap (fun p => qs.map fun q => (p,q)), t ≤ (u,v)) ↔
      (∃ p ∈ ps, p ≤ u) ∧ (∃ q ∈ qs, q ≤ v) := by
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨t, ⟨p,hp,q,hq,rfl⟩, ht⟩
      exact ⟨⟨p,hp,ht.1⟩,⟨q,hq,ht.2⟩⟩
    · rintro ⟨⟨p,hp,hu⟩,⟨q,hq,hv⟩⟩
      exact ⟨(p,q),⟨p,hp,q,hq,rfl⟩,hu,hv⟩
  rw [he]
  split_ifs <;> simp_all

#print axioms zetaSum_injective
#print axioms coefficient_factorization
#print axioms collected_union_product

end LC004
