import LC004.ChoiceAbstractCancellation

namespace LC004
open scoped Classical

/-- Changing equality decision procedures does not change the face sum. -/
theorem facetAlternatingSum_decidableEq {α : Type*} (F : Finset (Finset α))
    (d₁ d₂ : DecidableEq α) :
    faceAlternatingSum (@facetFaces α d₁ F) = faceAlternatingSum (@facetFaces α d₂ F) := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  cases h
  rfl

theorem choiceSolutionsClosed_decidableEq {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (d₁ d₂ : ∀ i, DecidableEq (D i)) :
    @ChoiceSolutionsClosed ι D d₁ A ↔ @ChoiceSolutionsClosed ι D d₂ A := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  cases h
  rfl

abbrev ChoiceSupport {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i : ι) := {x : D i // ∃ a ∈ A, a i = x}

noncomputable instance choiceSupport_fintype {ι : Type*} {D : ι → Type*}
    [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) (i : ι) :
    Fintype (ChoiceSupport A i) := Fintype.ofFinite _

def choiceSupportForget {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (b : ∀ i, ChoiceSupport A i) : ∀ i, D i :=
  fun i => (b i).val

def choiceSupportLift {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (a : ∀ i, D i) (ha : a ∈ A) : ∀ i, ChoiceSupport A i :=
  fun i => ⟨a i, a, ha, rfl⟩

theorem choiceSupportForget_injective {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) : Function.Injective (choiceSupportForget A) := by
  intro b c h
  funext i
  exact Subtype.ext (congrFun h i)

noncomputable def choiceSupportedFamily {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) :
    Finset (∀ i, ChoiceSupport A i) :=
  Finset.univ.filter (fun b => choiceSupportForget A b ∈ A)

theorem mem_choiceSupportedFamily {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (b : ∀ i, ChoiceSupport A i) :
    b ∈ choiceSupportedFamily A ↔ choiceSupportForget A b ∈ A := by
  simp [choiceSupportedFamily]

theorem choiceSupportLift_mem {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (a : ∀ i, D i) (ha : a ∈ A) : choiceSupportLift A a ha ∈ choiceSupportedFamily A := by
  exact (mem_choiceSupportedFamily A _).mpr ha

theorem choiceSupportedFamily_support {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) :
    ∀ i x, ∃ b ∈ choiceSupportedFamily A, b i = x := by
  intro i x
  obtain ⟨a, ha, hai⟩ := x.property
  exact ⟨choiceSupportLift A a ha, choiceSupportLift_mem A a ha, Subtype.ext hai⟩

theorem choiceSupportedFamily_pair {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (i j : ι) (x : ChoiceSupport A i) (y : ChoiceSupport A j) :
    ChoicePairProjection (choiceSupportedFamily A) i j x y ↔
      ChoicePairProjection A i j x.val y.val := by
  constructor
  · rintro ⟨b, hb, hbi, hbj⟩
    exact ⟨_, (mem_choiceSupportedFamily A b).mp hb,
      congrArg Subtype.val hbi, congrArg Subtype.val hbj⟩
  · rintro ⟨a, ha, hai, haj⟩
    exact ⟨choiceSupportLift A a ha, choiceSupportLift_mem A a ha,
      Subtype.ext hai, Subtype.ext haj⟩

theorem choiceSupportedFamily_binary {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (hbinary : ChoiceBinaryDetermined A) : ChoiceBinaryDetermined (choiceSupportedFamily A) := by
  intro b hpairs
  apply (mem_choiceSupportedFamily A b).mpr
  apply hbinary
  intro i j hij
  exact (choiceSupportedFamily_pair A i j _ _).mp (hpairs i j hij)

theorem choiceMajority_injective_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x y z : α) :
    f (choiceMajority x y z) = choiceMajority (f x) (f y) (f z) := by
  by_cases h : y = z
  · simp [choiceMajority, h]
  · have h' : f y ≠ f z := fun he => h (hf he)
    simp [choiceMajority, h, h']

theorem choiceSupportedFamily_closed {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (hclosed : ChoiceSolutionsClosed A) : ChoiceSolutionsClosed (choiceSupportedFamily A) := by
  intro a ha b hb c hc
  apply (mem_choiceSupportedFamily A _).mpr
  have h := hclosed _ ((mem_choiceSupportedFamily A a).mp ha)
    _ ((mem_choiceSupportedFamily A b).mp hb) _ ((mem_choiceSupportedFamily A c).mp hc)
  have heq : choiceSupportForget A (fun i => choiceMajority (a i) (b i) (c i)) =
      (fun i => choiceMajority (a i).val (b i).val (c i).val) := by
    funext i
    exact choiceMajority_injective_map Subtype.val Subtype.val_injective _ _ _
  rw [heq]
  exact h

theorem choiceSupportedFamily_card {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) :
    (choiceSupportedFamily A).card = A.card := by
  classical
  have himage : (choiceSupportedFamily A).image (choiceSupportForget A) = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact (mem_choiceSupportedFamily A b).mp hb
    · intro ha
      exact Finset.mem_image.mpr ⟨_, choiceSupportLift_mem A a ha, rfl⟩
  have hc := Finset.card_image_of_injective (choiceSupportedFamily A) (choiceSupportForget_injective A)
  rw [himage] at hc
  exact hc.symm

theorem choiceSupport_nontrivial {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i : ι)
    (h : ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i) : Nontrivial (ChoiceSupport A i) := by
  obtain ⟨a, ha, b, hb, hne⟩ := h
  exact ⟨⟨⟨a i, a, ha, rfl⟩, ⟨b i, b, hb, rfl⟩,
    fun he => hne (congrArg Subtype.val he)⟩⟩

noncomputable def choiceSupportEmbedding {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) : (Sigma (ChoiceSupport A)) ↪ Sigma D :=
  Function.Embedding.sigmaMap (Function.Embedding.refl ι)
    (fun _ => ⟨Subtype.val, Subtype.val_injective⟩)

theorem choiceFacet_support_image {ι : Type*} {D : ι → Type*}
    [Fintype ι] (A : Finset (∀ i, D i)) (b : ∀ i, ChoiceSupport A i) :
    (choiceFacet b).image (choiceSupportEmbedding A) = choiceFacet (choiceSupportForget A b) := by
  classical
  simp only [choiceFacet, Finset.image_image]
  rfl

theorem choiceFacets_support_image {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) :
    (choiceFacets (choiceSupportedFamily A)).image
      (fun f => f.image (choiceSupportEmbedding A)) = choiceFacets A := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨b, hb, rfl⟩ := (mem_choiceFacets _ g).mp hg
    rw [choiceFacet_support_image]
    exact (mem_choiceFacets A _).mpr ⟨_, (mem_choiceSupportedFamily A b).mp hb, rfl⟩
  · intro hf
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
    exact Finset.mem_image.mpr ⟨_,
      (mem_choiceFacets _ _).mpr ⟨_, choiceSupportLift_mem A a ha, rfl⟩,
      choiceFacet_support_image A (choiceSupportLift A a ha)⟩

theorem choiceAlternatingSum_supported {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i)) :
    faceAlternatingSum (facetFaces (choiceFacets A)) =
      faceAlternatingSum (facetFaces (choiceFacets (choiceSupportedFamily A))) := by
  rw [← choiceFacets_support_image A]
  exact facetAlternatingSum_image_embedding _ _ (choiceSupportEmbedding A).injective

#print axioms choiceSupportedFamily_binary
#print axioms choiceSupportedFamily_closed
#print axioms choiceSupportedFamily_card
#print axioms choiceAlternatingSum_supported
end LC004
