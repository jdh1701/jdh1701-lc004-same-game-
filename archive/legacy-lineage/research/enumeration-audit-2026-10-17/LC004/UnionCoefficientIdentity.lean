import LC004.CoefficientBarrier

namespace LC004

def joinWitnessLists {P : Type*} [SemilatticeSup P] (ps qs : List P) : List P :=
  ps.flatMap fun p => qs.map fun q => p ⊔ q

theorem zetaSum_add_sub {P : Type*} [Fintype P] [PartialOrder P]
    (a b c : P → ℤ) (x : P) :
    zetaSum (fun p => a p + b p - c p) x =
      zetaSum a x + zetaSum b x - zetaSum c x := by
  classical
  simp only [zetaSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p ≤ x <;> simp [h]

theorem joinWitnessLists_covered {P : Type*} [SemilatticeSup P]
    (ps qs : List P) (x : P) :
    (∃ r ∈ joinWitnessLists ps qs, r ≤ x) ↔
      (∃ p ∈ ps, p ≤ x) ∧ (∃ q ∈ qs, q ≤ x) := by
  simp only [joinWitnessLists, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨r,⟨p,hp,q,hq,rfl⟩,hr⟩
    exact ⟨⟨p,hp,(sup_le_iff.mp hr).1⟩,⟨q,hq,(sup_le_iff.mp hr).2⟩⟩
  · rintro ⟨⟨p,hp,hpx⟩,⟨q,hq,hqx⟩⟩
    exact ⟨p ⊔ q,⟨p,hp,q,hq,rfl⟩,sup_le hpx hqx⟩

/-- Inclusion-exclusion holds at each collected partition key, not only after
evaluating a colour count. This uses uniqueness of cumulative coefficients. -/
theorem collected_union_append {P : Type*} [Fintype P] [SemilatticeSup P]
    (ps qs : List P) (x : P) :
    collectedCoeff (unionTerms (· ⊔ ·) (ps ++ qs)) x =
      collectedCoeff (unionTerms (· ⊔ ·) ps) x +
      collectedCoeff (unionTerms (· ⊔ ·) qs) x -
      collectedCoeff (unionTerms (· ⊔ ·) (joinWitnessLists ps qs)) x := by
  classical
  have he : collectedCoeff (unionTerms (· ⊔ ·) (ps ++ qs)) =
      fun p => collectedCoeff (unionTerms (· ⊔ ·) ps) p +
        collectedCoeff (unionTerms (· ⊔ ·) qs) p -
        collectedCoeff (unionTerms (· ⊔ ·) (joinWitnessLists ps qs)) p := by
    apply zetaSum_injective
    intro p
    rw [zetaSum_add_sub]
    simp only [collected_union_zeta, joinWitnessLists_covered,
      List.mem_append, exists_or, or_and_right]
    by_cases hp : ∃ r ∈ ps, r ≤ p <;> by_cases hq : ∃ r ∈ qs, r ≤ p <;>
      simp [hp,hq]
  exact congrFun he x

/-- A fixed first component stays fixed in every join of a nonempty witness
subfamily; its coefficient is zero at any different first component. -/
theorem collected_union_fixed_first {P Q : Type*} [Fintype P] [Fintype Q]
    [SemilatticeSup P] [SemilatticeSup Q] (a x : P) (qs : List Q) (y : Q) :
    collectedCoeff (unionTerms (· ⊔ ·) (qs.map fun q => (a,q))) (x,y) =
      @ite ℤ (a=x) (Classical.propDecidable _) 1 0 *
        collectedCoeff (unionTerms (· ⊔ ·) qs) y := by
  classical
  have h := collected_union_product [a] qs x y
  have hs : collectedCoeff (unionTerms (· ⊔ ·) [a]) x =
      if a=x then 1 else 0 := by simp [unionTerms,addConstraint,collectedCoeff]
  rw [hs] at h
  by_cases hx : a=x <;> simpa [hx] using h

/-- When the two first-coordinate choices join to a genuinely different key,
the coefficient there is minus the coefficient of the intersection family. -/
theorem two_branch_join_coefficient {P Q : Type*} [Fintype P] [Fintype Q]
    [SemilatticeSup P] [SemilatticeSup Q] (a b : P) (ps qs : List Q)
    (ha : a ≠ a ⊔ b) (hb : b ≠ a ⊔ b) (y : Q) :
    collectedCoeff (unionTerms (· ⊔ ·)
      ((ps.map fun p => (a,p)) ++ (qs.map fun q => (b,q)))) (a ⊔ b,y) =
      -collectedCoeff (unionTerms (· ⊔ ·) (joinWitnessLists ps qs)) y := by
  classical
  rw [collected_union_append, collected_union_fixed_first, collected_union_fixed_first]
  have he : joinWitnessLists (ps.map fun p => (a,p)) (qs.map fun q => (b,q)) =
      (joinWitnessLists ps qs).map (fun r => (a ⊔ b,r)) := by
    simp [joinWitnessLists,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  rw [he,collected_union_fixed_first]
  simp [ha,hb]

/-- General two-branch cancellation. The geometric application must establish
that intersection coverage is unchanged by imposing the barrier. -/
theorem two_branch_barrier_zero {P Q : Type*} [Fintype P] [Fintype Q]
    [SemilatticeSup P] [Lattice Q] (a b : P) (ps qs : List Q)
    (ha : a ≠ a ⊔ b) (hb : b ≠ a ⊔ b) (barrier y : Q)
    (hinv : ∀ r,
      (∃ p ∈ joinWitnessLists ps qs, p ≤ r) ↔
      (∃ p ∈ joinWitnessLists ps qs, p ≤ r ⊓ barrier))
    (hy : ¬y ≤ barrier) :
    collectedCoeff (unionTerms (· ⊔ ·)
      ((ps.map fun p => (a,p)) ++ (qs.map fun q => (b,q)))) (a ⊔ b,y) = 0 := by
  classical
  rw [two_branch_join_coefficient a b ps qs ha hb y]
  have hz : collectedCoeff (unionTerms (· ⊔ ·) (joinWitnessLists ps qs)) y = 0 := by
    apply coefficient_zero_outside_barrier _ barrier _ y hy
    intro r
    simp only [collected_union_zeta]
    rw [hinv r]
  rw [hz,neg_zero]

#print axioms two_branch_join_coefficient
#print axioms two_branch_barrier_zero
#print axioms collected_union_append
#print axioms collected_union_fixed_first

end LC004
