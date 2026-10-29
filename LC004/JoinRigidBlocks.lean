import LC004.WinningConstraintGenerators

namespace LC004
open scoped Classical

theorem patternClassPositions_mono {n : Nat} {c x : ColorPattern n} (hcx : c ≤ x)
    (i : Fin n) : patternClassPositions c i ⊆ patternClassPositions x i := by
  intro j hj
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hcx hj

theorem mem_patternClassPositions_self {n : Nat} (c : ColorPattern n) (i : Fin n) :
    i ∈ patternClassPositions c i := by
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact c.refl' i

/-- R1: a refinement whose classes all have at least two elements agrees with the coarser
pattern on every class of size at most three. -/
theorem small_class_eq_of_refines {n : Nat} {c x : ColorPattern n}
    (hc : ∀ i, 2 ≤ (patternClassPositions c i).card) (hcx : c ≤ x) (i : Fin n)
    (h : (patternClassPositions x i).card ≤ 3) :
    patternClassPositions c i = patternClassPositions x i := by
  refine Finset.Subset.antisymm (patternClassPositions_mono hcx i) ?_
  intro e he
  by_contra hne
  have hsub1 : patternClassPositions c i ⊆ patternClassPositions x i :=
    patternClassPositions_mono hcx i
  have hsub2 : patternClassPositions c e ⊆ patternClassPositions x i := by
    intro j hj
    simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hj he ⊢
    exact x.trans' he (x.symm' (hcx hj))
  have hdisj : Disjoint (patternClassPositions c i) (patternClassPositions c e) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    apply hne
    simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2 ⊢
    exact c.trans' hj1 (c.symm' hj2)
  have hunion : patternClassPositions c i ∪ patternClassPositions c e ⊆
      patternClassPositions x i := Finset.union_subset hsub1 hsub2
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have h1 := hc i
  have h2 := hc e
  omega

end LC004
