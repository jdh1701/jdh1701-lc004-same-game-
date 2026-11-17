import LC004.FiveClassActualGeometry

namespace LC004

/-- Noncrossing of the full flattened family is exactly pairwise noncrossing
of distinct coordinate families, provided every coordinate has a partner. -/
theorem noncrossing_flatMap_iff_pairs {ι : Type*} (is : List ι)
    (B : ι → List (List Nat))
    (hpartner : ∀ i ∈ is, ∃ j ∈ is, i ≠ j) :
    NoncrossingBlockFamily (is.flatMap B) ↔
      ∀ i ∈ is, ∀ j ∈ is, i ≠ j → NoncrossingBlockFamily (B i ++ B j) := by
  constructor
  · intro h i hi j hj _ a ha b hb
    have hmem : ∀ c ∈ B i ++ B j, c ∈ is.flatMap B := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact List.mem_flatMap.mpr ⟨i,hi,hc⟩
      · exact List.mem_flatMap.mpr ⟨j,hj,hc⟩
    exact h a (hmem a ha) b (hmem b hb)
  · intro h a ha b hb
    obtain ⟨i,hi,hai⟩ := List.mem_flatMap.mp ha
    obtain ⟨j,hj,hbj⟩ := List.mem_flatMap.mp hb
    by_cases hij : i = j
    · subst j
      obtain ⟨j,hj,hij⟩ := hpartner i hi
      exact h i hi j hj hij a (List.mem_append_left _ hai) b (List.mem_append_left _ hbj)
    · exact h i hi j hj hij a (List.mem_append_left _ hai) b (List.mem_append_right _ hbj)

/-- The actual pair/triple blocks selected in every class. -/
def fiveClassAssignmentBlocks {k : Nat} (G : Fin k → Finset Nat) (a : Fin k → Fin 10) :
    List (List Nat) :=
  (List.finRange k).flatMap fun i => fiveSplitBlocks ((G i).sort (· ≤ ·)) (a i)

/-- Exactly the tuples whose selected pair/triple blocks form a noncrossing
family. No pairwise-constraint or closure hypothesis is part of the definition. -/
def fiveClassSplitFamily {k : Nat} (G : Fin k → Finset Nat) : Finset (Fin k → Fin 10) :=
  Finset.univ.filter fun a => finiteNoncrossing (fiveClassAssignmentBlocks G a) = true

theorem fiveClassSplitFamily_spec {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (a : Fin k → Fin 10) :
    a ∈ fiveClassSplitFamily G ↔
      ∀ i j, i ≠ j → FiveActualCompatible (G i) (G j) (a i) (a j) := by
  simp only [fiveClassSplitFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [finiteNoncrossing_iff]
  change NoncrossingBlockFamily ((List.finRange k).flatMap _) ↔ _
  rw [noncrossing_flatMap_iff_pairs]
  · simp only [List.mem_finRange, forall_const]
    rfl
  · intro i _
    obtain ⟨j,hj⟩ := exists_ne i
    exact ⟨j,List.mem_finRange j,Ne.symm hj⟩

/-- Connectedness stated directly in terms of crossing original color classes. -/
def FiveClassCrossingConnected {k : Nat} (G : Fin k → Finset Nat) : Prop :=
  ∀ S : Set (Fin k), S.Nonempty → Sᶜ.Nonempty →
    ∃ i ∈ S, ∃ j ∉ S, BlocksCross ((G i).sort (· ≤ ·)) ((G j).sort (· ≤ ·))

/-- Equality decision procedures do not affect conservative-majority closure. -/
theorem choiceRelationClosed_decidableEq {α β : Type*} (R : α → β → Prop)
    (d₁ d₂ : DecidableEq α) (e₁ e₂ : DecidableEq β) :
    @ChoiceRelationClosed α β d₁ e₁ R ↔ @ChoiceRelationClosed α β d₂ e₂ R := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  have he : e₁ = e₂ := Subsingleton.elim _ _
  cases hd
  cases he
  rfl

/-- Cancellation for actual noncrossing pair/triple split families of arbitrary
crossing-connected disjoint five-point classes. All abstract structural
hypotheses are now derived from the original class geometry. -/
theorem fiveClassSplitFamily_alternatingSum_zero {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hconn : FiveClassCrossingConnected G)
    (hthree : 3 ≤ (fiveClassSplitFamily G).card) :
    faceAlternatingSum (facetFaces (choiceFacets (fiveClassSplitFamily G))) = 0 := by
  let d₀ : DecidableEq (Fin 10) := inferInstance
  let d₁ : DecidableEq (Sigma (fun _ : Fin k => Fin 10)) := inferInstance
  classical
  have hclosed : ∀ i j, i ≠ j →
      @ChoiceRelationClosed (Fin 10) (Fin 10) (Classical.decEq _) (Classical.decEq _)
        (FiveActualCompatible (G i) (G j)) := by
    intro i j hij
    exact (choiceRelationClosed_decidableEq _ d₀ (Classical.decEq _) d₀ (Classical.decEq _)).mp
      (fiveClass_actual_geometry (G i) (G j) (hG i) (hG j) (hd i j hij)).1
  have hcuts : ∀ S : Set (Fin k), S.Nonempty → Sᶜ.Nonempty →
      ∃ i ∈ S, ∃ j ∉ S, ∃ p q : Fin 10,
        ∀ x y, FiveActualCompatible (G i) (G j) x y → x = p ∨ y = q := by
    intro S hS hSc
    obtain ⟨i,hi,j,hj,hcross⟩ := hconn S hS hSc
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    obtain ⟨p,q,hpq⟩ :=
      (fiveClass_actual_geometry (G i) (G j) (hG i) (hG j) (hd i j hij)).2 hcross
    exact ⟨i,hi,j,hj,p,q,hpq⟩
  have hz := choiceAlternatingSum_zero_of_covered_binary_spec (fiveClassSplitFamily G)
    (fun i j => FiveActualCompatible (G i) (G j)) (fiveClassSplitFamily_spec G) hclosed hcuts hthree
  let d₂ : DecidableEq (Sigma (fun _ : Fin k => Fin 10)) :=
    @Sigma.instDecidableEqSigma (Fin k) (fun _ => Fin 10)
      (Classical.decEq _) (fun _ => Classical.decEq _)
  exact (facetAlternatingSum_decidableEq (choiceFacets (fiveClassSplitFamily G)) d₁ d₂).trans hz

#print axioms fiveClassSplitFamily_spec
#print axioms fiveClassSplitFamily_alternatingSum_zero
end LC004
