import LC004.ChoiceComplexCancellation

namespace LC004

def ChoiceRelationClosed {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) : Prop :=
  ∀ x₁ y₁ x₂ y₂ x₃ y₃, R x₁ y₁ → R x₂ y₂ → R x₃ y₃ →
    R (choiceMajority x₁ x₂ x₃) (choiceMajority y₁ y₂ y₃)

def ChoiceRelationBijective {α β : Type*} (R : α → β → Prop) : Prop :=
  (∀ x, ∃! y, R x y) ∧ (∀ y, ∃! x, R x y)

def ChoiceRelationTwoFan {α β : Type*} (R : α → β → Prop) : Prop :=
  ∃ a b, ∀ x y, R x y ↔ x = a ∨ y = b

theorem choiceRelationClosed_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : α → β → Prop} (h : ChoiceRelationClosed R) :
    ChoiceRelationClosed (fun y x => R x y) := by
  intro y₁ x₁ y₂ x₂ y₃ x₃ h₁ h₂ h₃
  exact h x₁ y₁ x₂ y₂ x₃ y₃ h₁ h₂ h₃

theorem choiceRelation_row_one_or_all {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : α → β → Prop} (hclosed : ChoiceRelationClosed R)
    (hrows : ∀ x, ∃ y, R x y) (hcols : ∀ y, ∃ x, R x y) (x : α) :
    (∃! y, R x y) ∨ (∀ y, R x y) := by
  classical
  obtain ⟨y, hy⟩ := hrows x
  by_cases hu : ∀ z, R x z → z = y
  · exact Or.inl ⟨y, hy, hu⟩
  · push_neg at hu
    obtain ⟨z, hz, hzy⟩ := hu
    right
    intro w
    obtain ⟨u, huw⟩ := hcols w
    exact choiceMajority_closed_row_all R hclosed x u y z w hy hz hzy.symm huw

theorem choiceRelation_two_full_rows {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : α → β → Prop} (hclosed : ChoiceRelationClosed R)
    (hrows : ∀ x, ∃ y, R x y) {a b : α} (hab : a ≠ b)
    (ha : ∀ y, R a y) (hb : ∀ y, R b y) : ∀ x y, R x y := by
  intro x y
  obtain ⟨w, hxw⟩ := hrows x
  exact choiceMajority_closed_row_all (fun y x => R x y)
    (choiceRelationClosed_swap hclosed) y w a b x (ha y) (hb y) hab hxw

/-- Exact pair projections on supported, nonsingleton domains have only three
possible forms. This is an unbounded theorem, not a finite case computation. -/
theorem choiceRelation_classification {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Nontrivial β]
    {R : α → β → Prop} (hclosed : ChoiceRelationClosed R)
    (hrows : ∀ x, ∃ y, R x y) (hcols : ∀ y, ∃ x, R x y) :
    (∀ x y, R x y) ∨ ChoiceRelationBijective R ∨ ChoiceRelationTwoFan R := by
  classical
  by_cases huniv : ∀ x y, R x y
  · exact Or.inl huniv
  right
  by_cases hone : ∀ x, ∃! y, R x y
  · left
    refine ⟨hone, ?_⟩
    intro y
    obtain ⟨x, hxy⟩ := hcols y
    refine ⟨x, hxy, ?_⟩
    intro z hzy
    by_contra hzx
    have hfull : ∀ u, R u y := by
      intro u
      obtain ⟨w, huw⟩ := hrows u
      exact choiceMajority_closed_row_all (fun y x => R x y)
        (choiceRelationClosed_swap hclosed) y w x z u hxy hzy (Ne.symm hzx) huw
    obtain ⟨w, hwy⟩ := exists_ne y
    obtain ⟨u, huw⟩ := hcols w
    obtain ⟨v, _, hv⟩ := hone u
    exact hwy ((hv w huw).trans (hv y (hfull u)).symm)
  · right
    push_neg at hone
    obtain ⟨a, ha⟩ := hone
    have hfull : ∀ y, R a y :=
      (choiceRelation_row_one_or_all hclosed hrows hcols a).resolve_left ha
    have hnotall := huniv
    push_neg at hnotall
    obtain ⟨u, z, huz⟩ := hnotall
    have hua : u ≠ a := by intro h; subst u; exact huz (hfull z)
    obtain ⟨b, hub⟩ := hrows u
    have hcol : ∀ x, R x b := by
      intro x
      obtain ⟨w, hxw⟩ := hrows x
      exact choiceMajority_closed_row_all (fun y x => R x y)
        (choiceRelationClosed_swap hclosed) b w a u x (hfull b) hub hua.symm hxw
    refine ⟨a, b, ?_⟩
    intro x y
    constructor
    · intro hxy
      by_cases hxa : x = a
      · exact Or.inl hxa
      · right
        have hxnot : ¬ ∀ t, R x t := by
          intro hxfull
          exact huniv (choiceRelation_two_full_rows hclosed hrows (Ne.symm hxa) hfull hxfull)
        obtain ⟨t, _, ht⟩ :=
          (choiceRelation_row_one_or_all hclosed hrows hcols x).resolve_right hxnot
        exact (ht y hxy).trans (ht b (hcol x)).symm
    · rintro (rfl | rfl)
      · exact hfull y
      · exact hcol x

/-- A mutually forcing pair of values forces a bijection of their entire
supported domains. This is the step needed to eliminate implication cycles. -/
theorem choiceRelation_bijective_of_isolated_pair {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Nontrivial α] [Nontrivial β]
    {R : α → β → Prop} (hclosed : ChoiceRelationClosed R)
    (hrows : ∀ x, ∃ y, R x y) (hcols : ∀ y, ∃ x, R x y)
    (a : α) (b : β) (hrow : ∀ y, R a y → y = b)
    (hcol : ∀ x, R x b → x = a) : ChoiceRelationBijective R := by
  rcases choiceRelation_classification hclosed hrows hcols with hu | hb | hf
  · obtain ⟨y, hy⟩ := exists_ne b
    exact (hy (hrow y (hu a y))).elim
  · exact hb
  · obtain ⟨x, y, hf⟩ := hf
    have hyb : y = b := hrow y ((hf a y).mpr (Or.inr rfl))
    have hxa : x = a := hcol x (hyb ▸ (hf x y).mpr (Or.inl rfl))
    obtain ⟨z, hz⟩ := exists_ne b
    have haz : R a z := (hf a z).mpr (Or.inl hxa.symm)
    exact (hz (hrow z haz)).elim

#print axioms choiceRelation_classification
#print axioms choiceRelation_bijective_of_isolated_pair
end LC004
