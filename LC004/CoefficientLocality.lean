import LC004.CoefficientFactorization

namespace LC004

/-- A coefficient at `p` is determined by cumulative values only below `p`. -/
theorem zetaSum_injective_below {P : Type*} [Fintype P] [PartialOrder P]
    {a b : P → ℤ} (p : P) (hab : ∀ x, x ≤ p → zetaSum a x = zetaSum b x) :
    a p = b p := by
  classical
  have wf : WellFounded ((· < ·) : P → P → Prop) := wellFounded_lt
  have hlocal : ∀ x, x ≤ p → a x = b x := by
    intro x
    induction x using wf.induction with
    | h x ih =>
      intro hxp
      have hd : (∑ y, if y ≤ x then a y - b y else 0) = 0 := by
        have he : (∑ y, if y ≤ x then a y - b y else 0) =
            zetaSum a x - zetaSum b x := by
          simp only [zetaSum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          split_ifs <;> simp
        rw [he, hab x hxp, sub_self]
      have he : (∑ y, if y ≤ x then a y - b y else 0) = a x - b x := by
        rw [Finset.sum_eq_single x]
        · simp
        · intro y hy hne
          by_cases hle : y ≤ x
          · simp [hle, ih y (lt_of_le_of_ne hle hne) (le_trans hle hxp)]
          · simp [hle]
        · simp
      exact sub_eq_zero.mp (he.symm.trans hd)
  exact hlocal p le_rfl

/-- Lists giving the same witness coverage below a target have the same
coefficient at that target, regardless of order, duplication, or witnesses above it. -/
theorem collected_union_congr_below {P : Type*} [Fintype P] [SemilatticeSup P]
    (ps qs : List P) (p : P)
    (h : ∀ x, x ≤ p → ((∃ r ∈ ps, r ≤ x) ↔ (∃ r ∈ qs, r ≤ x))) :
    collectedCoeff (unionTerms (· ⊔ ·) ps) p =
      collectedCoeff (unionTerms (· ⊔ ·) qs) p := by
  apply zetaSum_injective_below p
  intro x hxp
  simp only [collected_union_zeta]
  rw [h x hxp]

/-- Witnesses not refining a target partition can be discarded for its
coefficient. No assumption about the particular witness family is required. -/
theorem collected_union_filter_le {P : Type*} [Fintype P] [SemilatticeSup P]
    (ps : List P) (p : P) :
    collectedCoeff (unionTerms (· ⊔ ·) ps) p =
      collectedCoeff (unionTerms (· ⊔ ·)
        (ps.filter (fun r => @decide (r ≤ p) (Classical.propDecidable _)))) p := by
  classical
  apply collected_union_congr_below
  intro x hxp
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨r,hr,hrx⟩
    exact ⟨r,⟨hr,le_trans hrx hxp⟩,hrx⟩
  · rintro ⟨r,⟨hr,_⟩,hrx⟩
    exact ⟨r,hr,hrx⟩

end LC004
