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
    exact x.trans' he (hcx hj)
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

theorem mem_patternClassPositions_iff {n : Nat} (c : ColorPattern n) (i j : Fin n) :
    j ∈ patternClassPositions c i ↔ c i j := by
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- R2: in a join of pair/triple certificates, a class of size at most three is never crossed
by another class. -/
theorem join_small_class_no_cross {n : Nat} {F : Finset (ColorPattern n)}
    {x : ColorPattern n} (hF : ∀ c ∈ F, CertificateConstraint c) (hle : ∀ c ∈ F, c ≤ x)
    (hmin : ∀ y : ColorPattern n, (∀ c ∈ F, c ≤ y) → x ≤ y)
    {u v w z : Fin n} (huv : u < v) (hxuv : x u v)
    (hsmall : (patternClassPositions x u).card ≤ 3)
    (hwz : x w z) (huw : u < w) (hwv : w < v) (hz : ¬ (u < z ∧ z < v))
    (hnz : ¬ x u z) : False := by
  have hcuv : ∀ c ∈ F, c u v := by
    intro c hc
    have heq := small_class_eq_of_refines
      (fun i => by have := (hF c hc).1 i; omega) (hle c hc) u hsmall
    have hv : v ∈ patternClassPositions x u := (mem_patternClassPositions_iff x u v).2 hxuv
    rw [← heq] at hv
    exact (mem_patternClassPositions_iff c u v).1 hv
  let S : Fin n → Prop := fun i => u < i ∧ i < v ∧ ¬ x u i
  have claim : ∀ c ∈ F, ∀ i j, c i j → S i → S j := by
    intro c hc i j hij hSi
    obtain ⟨hui, hiv, hxi⟩ := hSi
    have hNC := (hF c hc).2
    have hcu : ∀ k, c u k → x u k := fun k h => hle c hc h
    have hcuv' := hcuv c hc
    have huj : u < j := by
      rcases lt_trichotomy j u with h | h | h
      · exfalso
        have h1 : c j u := hNC j u i v h hui hiv (c.symm' hij) hcuv'
        exact hxi (hcu i (c.trans' (c.symm' h1) (c.symm' hij)))
      · exfalso; subst h; exact hxi (hcu i (c.symm' hij))
      · exact h
    have hjv : j < v := by
      rcases lt_trichotomy j v with h | h | h
      · exact h
      · exfalso; subst h; exact hxi (hcu i (c.trans' hcuv' (c.symm' hij)))
      · exfalso
        have h1 : c u i := hNC u i v j hui hiv h hcuv' hij
        exact hxi (hcu i h1)
    refine ⟨huj, hjv, fun h => hxi ?_⟩
    exact x.trans' h (x.symm' (hle c hc hij))
  let y : Setoid (Fin n) := ⟨fun i j => S i ↔ S j,
    ⟨fun _ => Iff.rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
  have hy : ∀ c ∈ F, c ≤ y := by
    intro c hc a b hab
    exact ⟨claim c hc a b hab, claim c hc b a (c.symm' hab)⟩
  have hxy : x ≤ y := hmin y hy
  have hSw : S w := ⟨huw, hwv, fun h => hnz (x.trans' h hwz)⟩
  have h2 : S w ↔ S z := hxy hwz
  exact hz ⟨(h2.1 hSw).1, (h2.1 hSw).2.1⟩

end LC004
