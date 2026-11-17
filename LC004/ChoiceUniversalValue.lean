import LC004.ChoiceRelationClassification

namespace LC004

def ChoiceSolutionsClosed {ι : Type*} {D : ι → Type*} [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    (fun i => choiceMajority (a i) (b i) (c i)) ∈ A

def ChoicePairProjection {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i j : ι) (x : D i) (y : D j) : Prop :=
  ∃ a ∈ A, a i = x ∧ a j = y

noncomputable def choiceValueFiber {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i : ι) (x : D i) : Finset (∀ i, D i) := by
  classical
  exact A.filter (fun a => a i = x)

theorem mem_choiceValueFiber {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i : ι) (x : D i) (a : ∀ i, D i) :
    a ∈ choiceValueFiber A i x ↔ a ∈ A ∧ a i = x := by
  classical
  simp [choiceValueFiber]

theorem choicePairProjection_swap {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i j : ι) (x : D i) (y : D j) :
    ChoicePairProjection A i j x y ↔ ChoicePairProjection A j i y x := by
  simp only [ChoicePairProjection, and_comm]

theorem choicePairProjection_closed {ι : Type*} {D : ι → Type*}
    [∀ i, DecidableEq (D i)] {A : Finset (∀ i, D i)}
    (hclosed : ChoiceSolutionsClosed A) (i j : ι) :
    ChoiceRelationClosed (ChoicePairProjection A i j) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃ h₁ h₂ h₃
  obtain ⟨a, ha, hai, haj⟩ := h₁
  obtain ⟨b, hb, hbi, hbj⟩ := h₂
  obtain ⟨c, hc, hci, hcj⟩ := h₃
  refine ⟨_, hclosed a ha b hb c hc, ?_, ?_⟩
  · simp [hai, hbi, hci]
  · simp [haj, hbj, hcj]

/-- On supported finite domains, once all bijectively linked coordinates have
been eliminated, some value is compatible with every value in every other
coordinate. Choosing a largest fiber replaces the paper's acyclic-graph step. -/
theorem choice_exists_universal_value {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nonempty ι] [∀ i, Fintype (D i)]
    [∀ i, DecidableEq (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hclosed : ChoiceSolutionsClosed A)
    (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hnobij : ∀ i j, i ≠ j → ¬ ChoiceRelationBijective (ChoicePairProjection A i j)) :
    ∃ i x, ∀ j, i ≠ j → ∀ y, ChoicePairProjection A i j x y := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨x₀, _, _⟩ := exists_pair_ne (D i₀)
  have hne : (Finset.univ : Finset (Sigma D)).Nonempty :=
    ⟨⟨i₀, x₀⟩, Finset.mem_univ _⟩
  obtain ⟨⟨i, x⟩, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Sigma D))
    (fun v => (choiceValueFiber A v.1 v.2).card) hne
  refine ⟨i, x, ?_⟩
  intro j hij y
  have hrows : ∀ u, ∃ v, ChoicePairProjection A i j u v := by
    intro u
    obtain ⟨a, ha, hai⟩ := hsupport i u
    exact ⟨a j, a, ha, hai, rfl⟩
  have hcols : ∀ v, ∃ u, ChoicePairProjection A i j u v := by
    intro v
    obtain ⟨a, ha, haj⟩ := hsupport j v
    exact ⟨a i, a, ha, rfl, haj⟩
  have hrel := choicePairProjection_closed hclosed i j
  rcases choiceRelation_row_one_or_all hrel hrows hcols x with hone | hall
  · obtain ⟨z, _, hz⟩ := hone
    have hsub : choiceValueFiber A i x ⊆ choiceValueFiber A j z := by
      intro a ha
      obtain ⟨ha, hai⟩ := (mem_choiceValueFiber A i x a).mp ha
      exact (mem_choiceValueFiber A j z a).mpr
        ⟨ha, hz (a j) ⟨a, ha, hai, rfl⟩⟩
    have heq : choiceValueFiber A i x = choiceValueFiber A j z :=
      Finset.eq_of_subset_of_card_le hsub (hmax ⟨j, z⟩ (Finset.mem_univ _))
    have hcol : ∀ u, ChoicePairProjection A i j u z → u = x := by
      intro u hu
      obtain ⟨a, ha, hai, haj⟩ := hu
      have hm : a ∈ choiceValueFiber A i x := by
        rw [heq]
        exact (mem_choiceValueFiber A j z a).mpr ⟨ha, haj⟩
      exact hai.symm.trans ((mem_choiceValueFiber A i x a).mp hm).2
    exact (hnobij i j hij
      (choiceRelation_bijective_of_isolated_pair hrel hrows hcols x z hz hcol)).elim
  · exact hall y

/-- The binary-extension hypothesis is explicit; it does not hold for an
arbitrary family of tuples merely because its pair projections look compatible. -/
def ChoiceBinaryDetermined {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) : Prop :=
  ∀ a, (∀ i j, i ≠ j → ChoicePairProjection A i j (a i) (a j)) → a ∈ A

theorem choiceBinaryDetermined_of_binary_constraints {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j)) :
    ChoiceBinaryDetermined A := by
  intro a hlocal
  apply (hspec a).mpr
  intro i j hij
  obtain ⟨b, hb, hbi, hbj⟩ := hlocal i j hij
  simpa [hbi, hbj] using (hspec b).mp hb i j hij

theorem choice_universal_value_replace {ι : Type*} {D : ι → Type*}
    [DecidableEq ι] (A : Finset (∀ i, D i))
    (hbinary : ChoiceBinaryDetermined A) (i : ι) (x : D i)
    (hfull : ∀ j, i ≠ j → ∀ y, ChoicePairProjection A i j x y)
    (a : ∀ i, D i) (ha : a ∈ A) : Function.update a i x ∈ A := by
  apply hbinary
  intro k l hkl
  by_cases hk : k = i
  · subst k
    simpa [Function.update_of_ne (Ne.symm hkl)] using hfull l hkl (a l)
  · by_cases hl : l = i
    · subst l
      have h := (choicePairProjection_swap A i k x (a k)).mp
        (hfull k (Ne.symm hk) (a k))
      simpa [Function.update_of_ne hk] using h
    · have h : ChoicePairProjection A k l (a k) (a l) := ⟨a, ha, rfl, rfl⟩
      simpa [Function.update_of_ne hk, Function.update_of_ne hl] using h

#print axioms choicePairProjection_closed
#print axioms choice_exists_universal_value
#print axioms choiceBinaryDetermined_of_binary_constraints
#print axioms choice_universal_value_replace
end LC004
