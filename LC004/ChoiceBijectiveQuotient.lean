import LC004.ChoiceCoordinateReduction

namespace LC004
open scoped Classical

theorem choicePair_bijective_iff_determines {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) (i j : ι) :
    ChoiceRelationBijective (ChoicePairProjection A i j) ↔
      (∀ a ∈ A, ∀ b ∈ A, a i = b i → a j = b j) ∧
      (∀ a ∈ A, ∀ b ∈ A, a j = b j → a i = b i) := by
  constructor
  · intro h
    constructor
    · intro a ha b hb hab
      obtain ⟨y, _, hy⟩ := h.1 (a i)
      exact (hy (a j) ⟨a, ha, rfl, rfl⟩).trans
        (hy (b j) ⟨b, hb, hab.symm, rfl⟩).symm
    · intro a ha b hb hab
      obtain ⟨x, _, hx⟩ := h.2 (a j)
      exact (hx (a i) ⟨a, ha, rfl, rfl⟩).trans
        (hx (b i) ⟨b, hb, rfl, hab.symm⟩).symm
  · rintro ⟨hij, hji⟩
    constructor
    · intro x
      obtain ⟨a, ha, hai⟩ := hsupport i x
      refine ⟨a j, ⟨a, ha, hai, rfl⟩, ?_⟩
      rintro y ⟨b, hb, hbi, hbj⟩
      exact hbj.symm.trans (hij b hb a ha (hbi.trans hai.symm))
    · intro y
      obtain ⟨a, ha, haj⟩ := hsupport j y
      refine ⟨a i, ⟨a, ha, rfl, haj⟩, ?_⟩
      rintro x ⟨b, hb, hbi, hbj⟩
      exact hbi.symm.trans (hji b hb a ha (hbj.trans haj.symm))

def choiceBijectiveSetoid {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) : Setoid ι where
  r i j := ChoiceRelationBijective (ChoicePairProjection A i j)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (choicePair_bijective_iff_determines A hsupport i i).mpr
        ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
    · intro i j h
      have hd := (choicePair_bijective_iff_determines A hsupport i j).mp h
      exact (choicePair_bijective_iff_determines A hsupport j i).mpr ⟨hd.2, hd.1⟩
    · intro i j k hij hjk
      have h₁ := (choicePair_bijective_iff_determines A hsupport i j).mp hij
      have h₂ := (choicePair_bijective_iff_determines A hsupport j k).mp hjk
      exact (choicePair_bijective_iff_determines A hsupport i k).mpr
        ⟨fun a ha b hb h => h₂.1 a ha b hb (h₁.1 a ha b hb h),
         fun a ha b hb h => h₁.2 a ha b hb (h₂.2 a ha b hb h)⟩

noncomputable def choiceRelationEquiv {α β : Type*} (R : α → β → Prop)
    (h : ChoiceRelationBijective R) : α ≃ β where
  toFun x := Classical.choose (h.1 x)
  invFun y := Classical.choose (h.2 y)
  left_inv x := ((Classical.choose_spec (h.2 _)).2 x
    (Classical.choose_spec (h.1 x)).1).symm
  right_inv y := ((Classical.choose_spec (h.1 _)).2 y
    (Classical.choose_spec (h.2 y)).1).symm

theorem choiceRelationEquiv_graph {α β : Type*} (R : α → β → Prop)
    (h : ChoiceRelationBijective R) (x : α) (y : β) :
    R x y ↔ choiceRelationEquiv R h x = y := by
  constructor
  · intro hxy
    exact ((Classical.choose_spec (h.1 x)).2 y hxy).symm
  · intro heq
    rw [← heq]
    exact (Classical.choose_spec (h.1 x)).1

abbrev ChoiceCoordinateQuotient {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :=
  Quotient (choiceBijectiveSetoid A hsupport)

noncomputable instance choiceCoordinateQuotient_fintype {ι : Type*} {D : ι → Type*}
    [Fintype ι] (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    Fintype (ChoiceCoordinateQuotient A hsupport) := Fintype.ofFinite _

noncomputable def choiceQuotientEquiv {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) (i : ι) :
    D ((Quotient.mk (choiceBijectiveSetoid A hsupport) i).out) ≃ D i :=
  choiceRelationEquiv (ChoicePairProjection A
    (Quotient.mk (choiceBijectiveSetoid A hsupport) i).out i)
    (@Quotient.mk_out ι (choiceBijectiveSetoid A hsupport) i)

theorem choiceQuotientEquiv_on_solution {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (a : ∀ i, D i) (ha : a ∈ A) (i : ι) :
    choiceQuotientEquiv A hsupport i
      (a ((Quotient.mk (choiceBijectiveSetoid A hsupport) i).out)) = a i := by
  unfold choiceQuotientEquiv
  apply (choiceRelationEquiv_graph _ _ _ _).mp
  exact ⟨a, ha, rfl, rfl⟩

/-- Every original solution is the lift of its values at chosen representatives;
this discharges the coherence hypothesis of the generic reduction lemmas. -/
theorem choiceQuotient_covers {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    ∀ a ∈ A, ∃ b : ∀ q : ChoiceCoordinateQuotient A hsupport, D q.out,
      choiceCoordinateLift (Quotient.mk _) (choiceQuotientEquiv A hsupport) b = a := by
  intro a ha
  refine ⟨fun q => a q.out, ?_⟩
  funext i
  exact choiceQuotientEquiv_on_solution A hsupport a ha i

noncomputable def choiceQuotientFamily {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    Finset (∀ q : ChoiceCoordinateQuotient A hsupport, D q.out) :=
  choiceReducedFamily A (Quotient.mk _) (choiceQuotientEquiv A hsupport)

theorem choiceQuotientFamily_support {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    ∀ q x, ∃ b ∈ choiceQuotientFamily A hsupport, b q = x :=
  choiceReducedFamily_support A _ _ Quotient.mk_surjective hsupport
    (choiceQuotient_covers A hsupport)

theorem choiceQuotientFamily_binary {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hbinary : ChoiceBinaryDetermined A) :
    ChoiceBinaryDetermined (choiceQuotientFamily A hsupport) :=
  choiceReducedFamily_binary A _ _ Quotient.mk_surjective hsupport
    (choiceQuotient_covers A hsupport) hbinary

theorem choiceQuotientFamily_connected {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hconn : ChoiceCoordinatesConnected A) :
    ChoiceCoordinatesConnected (choiceQuotientFamily A hsupport) :=
  choiceReducedFamily_connected A _ _ Quotient.mk_surjective
    (choiceQuotient_covers A hsupport) hconn

theorem choiceQuotientFamily_closed {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hclosed : ChoiceSolutionsClosed A) :
    ChoiceSolutionsClosed (choiceQuotientFamily A hsupport) :=
  choiceReducedFamily_closed A _ _ hclosed

theorem choiceRelationBijective_relabel {α β γ δ : Type*}
    (R : γ → δ → Prop) (e : α ≃ γ) (f : β ≃ δ) :
    ChoiceRelationBijective (fun x y => R (e x) (f y)) ↔ ChoiceRelationBijective R := by
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · intro a
      obtain ⟨x, rfl⟩ := e.surjective a
      exact f.existsUnique_congr_right.mp (hx x)
    · intro b
      obtain ⟨y, rfl⟩ := f.surjective b
      exact e.existsUnique_congr_right.mp (hy y)
  · rintro ⟨hx, hy⟩
    exact ⟨fun x => f.existsUnique_congr_right.mpr (hx (e x)),
      fun y => e.existsUnique_congr_right.mpr (hy (f y))⟩

/-- Distinct quotient coordinates cannot remain bijectively linked. -/
theorem choiceQuotientFamily_no_bijections {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    ∀ q t, q ≠ t → ¬ ChoiceRelationBijective
      (ChoicePairProjection (choiceQuotientFamily A hsupport) q t) := by
  intro q t hqt hbij
  let r := Quotient.mk (choiceBijectiveSetoid A hsupport)
  let e := choiceQuotientEquiv A hsupport
  have hq : r q.out = q := Quotient.out_eq q
  have ht : r t.out = t := Quotient.out_eq t
  have hb : ChoiceRelationBijective
      (ChoicePairProjection (choiceReducedFamily (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) A r e) (r q.out) (r t.out)) := by
    change ChoiceRelationBijective
      (ChoicePairProjection (choiceQuotientFamily A hsupport) (r q.out) (r t.out))
    rw [hq, ht]
    exact hbij
  have heq : (fun x y => ChoicePairProjection A q.out t.out (e q.out x) (e t.out y)) =
      ChoicePairProjection (choiceReducedFamily (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) A r e) (r q.out) (r t.out) := by
    funext x y
    exact propext (choiceReducedFamily_pair (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) A r e (choiceQuotient_covers A hsupport)
      q.out t.out x y).symm
  rw [← heq] at hb
  have hold := (choiceRelationBijective_relabel _ (e q.out) (e t.out)).mp hb
  have hsound : r q.out = r t.out := Quotient.sound hold
  exact hqt (hq.symm.trans (hsound.trans ht))

theorem choiceQuotientFamily_card {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    (choiceQuotientFamily A hsupport).card = A.card := by
  classical
  let r := Quotient.mk (choiceBijectiveSetoid A hsupport)
  let e := choiceQuotientEquiv A hsupport
  let B := choiceQuotientFamily A hsupport
  have himage : B.image (choiceCoordinateLift (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) r e) = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact (mem_choiceReducedFamily (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) A r e b).mp hb
    · intro ha
      obtain ⟨b, hb⟩ := choiceQuotient_covers A hsupport a ha
      exact Finset.mem_image.mpr
        ⟨b, (mem_choiceReducedFamily (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) A r e b).mpr (hb.symm ▸ ha), hb⟩
  have hinj := choiceCoordinateLift_injective (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) r e Quotient.mk_surjective
  have hc : (B.image (choiceCoordinateLift (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out) r e)).card = B.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h)
  exact hc.symm.trans (congrArg Finset.card himage)

theorem choiceQuotientFamily_alternatingSum_zero {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    [Nontrivial (ChoiceCoordinateQuotient A hsupport)]
    (hclosed : ChoiceSolutionsClosed A) (hbinary : ChoiceBinaryDetermined A)
    (hconn : ChoiceCoordinatesConnected A) :
    faceAlternatingSum (facetFaces (choiceFacets (choiceQuotientFamily A hsupport))) = 0 := by
  apply choiceAlternatingSum_zero_of_reduced_system
  · exact choiceQuotientFamily_closed A hsupport hclosed
  · exact choiceQuotientFamily_support A hsupport
  · exact choiceQuotientFamily_binary A hsupport hbinary
  · exact choiceQuotientFamily_no_bijections A hsupport
  · exact choiceCoordinatesConnected_neighbors _ (choiceQuotientFamily_connected A hsupport hconn)

#print axioms choiceBijectiveSetoid
#print axioms choiceQuotient_covers
#print axioms choiceQuotientFamily_binary
#print axioms choiceQuotientFamily_connected
#print axioms choiceQuotientFamily_no_bijections
#print axioms choiceQuotientFamily_card
#print axioms choiceQuotientFamily_alternatingSum_zero
end LC004
