import LC004.FiveClassSplitCancellation

namespace LC004
open scoped BigOperators Classical

theorem faceAlternatingSum_twoFacets {α : Type*} [DecidableEq α]
    (F G : Finset α) (hF : F.Nonempty) (hG : G.Nonempty) :
    faceAlternatingSum (facetFaces {F,G}) = if F ∩ G = ∅ then -1 else 0 := by
  classical
  have hi : F.powerset ∩ G.powerset = (F ∩ G).powerset := by
    ext s
    simp only [Finset.mem_inter, Finset.mem_powerset, Finset.subset_inter_iff]
  have hs := Finset.sum_union_inter (s₁ := F.powerset) (s₂ := G.powerset)
    (f := fun s : Finset α => (-1 : Int) ^ s.card)
  rw [hi, Finset.sum_powerset_neg_one_pow_card,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hF,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hG] at hs
  have hf : facetFaces {F,G} = F.powerset ∪ G.powerset := by simp [facetFaces]
  rw [hf]
  unfold faceAlternatingSum
  split_ifs with h <;> simp only [h, if_true, if_false] at hs <;> omega

theorem choiceFacet_nonempty {ι : Type*} {D : ι → Type*} [Fintype ι] [Nonempty ι]
    (a : ∀ i, D i) : (choiceFacet a).Nonempty := by
  classical
  let i := Classical.arbitrary ι
  exact ⟨⟨i,a i⟩,(mem_choiceFacet a i (a i)).mpr rfl⟩

theorem choiceFacet_inter_empty_iff {ι : Type*} {D : ι → Type*} [Fintype ι]
    [DecidableEq (Sigma D)] (a b : ∀ i, D i) : choiceFacet a ∩ choiceFacet b = ∅ ↔ ∀ i, a i ≠ b i := by
  classical
  constructor
  · intro h i hab
    have hm : Sigma.mk i (a i) ∈ choiceFacet a ∩ choiceFacet b := by
      exact Finset.mem_inter.mpr ⟨(mem_choiceFacet a i (a i)).mpr rfl,
        (mem_choiceFacet b i (a i)).mpr hab.symm⟩
    rw [h] at hm
    exact Finset.not_mem_empty _ hm
  · intro h
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    rintro ⟨i,x⟩ hx
    have ha := (mem_choiceFacet a i x).mp (Finset.mem_inter.mp hx).1
    have hb := (mem_choiceFacet b i x).mp (Finset.mem_inter.mp hx).2
    exact h i (ha.trans hb.symm)

theorem choiceAlternatingSum_two {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq (∀ i, D i)] [DecidableEq (Sigma D)]
    (a b : ∀ i, D i) :
    faceAlternatingSum (facetFaces (choiceFacets {a,b})) =
      if (∀ i, a i ≠ b i) then -1 else 0 := by
  classical
  have he : choiceFacets ({a,b} : Finset (∀ i, D i)) = {choiceFacet a,choiceFacet b} := by
    ext f
    simp [choiceFacets]
  rw [he,faceAlternatingSum_twoFacets _ _ (choiceFacet_nonempty a) (choiceFacet_nonempty b)]
  by_cases h : ∀ i, a i ≠ b i
  · rw [if_pos h,if_pos ((choiceFacet_inter_empty_iff a b).mpr h)]
  · rw [if_neg h,if_neg (fun he => h ((choiceFacet_inter_empty_iff a b).mp he))]

theorem choiceAlternatingSum_zero_of_constant_with_eq {ι : Type*} {D : ι → Type*}
    [Fintype ι] [DecidableEq (Sigma D)] (A : Finset (∀ i, D i)) (i : ι) (x : D i)
    (hconstant : ∀ a ∈ A, a i = x) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  classical
  apply faceAlternatingSum_zero_of_cone _ (Sigma.mk i x)
  · intro s hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
    exact (mem_facetFaces _ _).mpr ⟨f,hf,(Finset.erase_subset _ _).trans hsf⟩
  · intro s hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
    obtain ⟨a,ha,rfl⟩ := mem_choiceFacets A f |>.mp hf
    have hw : Sigma.mk i x ∈ choiceFacet a := (mem_choiceFacet a i x).mpr (hconstant a ha)
    exact (mem_facetFaces _ _).mpr
      ⟨choiceFacet a, (mem_choiceFacets A _).mpr ⟨a,ha,rfl⟩, Finset.insert_subset hw hsf⟩

theorem choiceAlternatingSum_of_subsingleton {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq (∀ i, D i)] [DecidableEq (Sigma D)]
    (A : Finset (∀ i, D i)) (hA : A.card ≤ 1) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  classical
  by_cases he : A = ∅
  · subst A
    simp [choiceFacets,facetFaces,faceAlternatingSum]
  · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    let i := Classical.arbitrary ι
    apply choiceAlternatingSum_zero_of_constant_with_eq A i (a i)
    intro b hb
    have hab : a = b := (Finset.card_le_one.mp hA) a ha b hb
    exact congrFun hab.symm i

/-- Once the >=3 case is cancelled, the entire law is decided by separated
pairs. A shared coordinate makes the two-certificate complex a cone. -/
theorem choiceAlternatingSum_classification {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq (∀ i, D i)] [DecidableEq (Sigma D)]
    (A : Finset (∀ i, D i))
    (hlarge : 3 ≤ A.card → faceAlternatingSum (facetFaces (choiceFacets A)) = 0) :
    faceAlternatingSum (facetFaces (choiceFacets A)) =
      if (∃ a b, A = {a,b} ∧ ∀ i, a i ≠ b i) then -1 else 0 := by
  classical
  by_cases hp : ∃ a b, A = {a,b} ∧ ∀ i, a i ≠ b i
  · obtain ⟨a,b,he,hs⟩ := hp
    rw [if_pos ⟨a,b,he,hs⟩,he,choiceAlternatingSum_two,if_pos hs]
  · rw [if_neg hp]
    by_cases hl : 3 ≤ A.card
    · exact hlarge hl
    · by_cases hs : A.card ≤ 1
      · exact choiceAlternatingSum_of_subsingleton A hs
      · have ht : A.card = 2 := by omega
        obtain ⟨a,b,_,he⟩ := Finset.card_eq_two.mp ht
        have hn : ¬ ∀ i, a i ≠ b i := fun h => hp ⟨a,b,he,h⟩
        push_neg at hn
        obtain ⟨i,hi⟩ := hn
        apply choiceAlternatingSum_zero_of_constant_with_eq A i (a i)
        intro c hc
        rw [he] at hc
        simp only [Finset.mem_insert,Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · rfl
        · exact hi.symm

/-- Complete boundary and cancellation law for actual five-class split
certificates, uniformly in the number and spacing of the classes. -/
theorem fiveClassSplitFamily_alternatingSum_classification {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hconn : FiveClassCrossingConnected G) :
    faceAlternatingSum (facetFaces (choiceFacets (fiveClassSplitFamily G))) =
      if (∃ a b, fiveClassSplitFamily G = {a,b} ∧ ∀ i, a i ≠ b i) then -1 else 0 := by
  have hc := choiceAlternatingSum_classification (fiveClassSplitFamily G)
    (fiveClassSplitFamily_alternatingSum_zero G hG hd hconn)
  by_cases hp : ∃ a b, fiveClassSplitFamily G = {a,b} ∧ ∀ i, a i ≠ b i
  · rw [if_pos hp] at hc ⊢
    exact hc
  · rw [if_neg hp] at hc ⊢
    exact hc

#print axioms choiceAlternatingSum_classification
#print axioms fiveClassSplitFamily_alternatingSum_classification
end LC004
