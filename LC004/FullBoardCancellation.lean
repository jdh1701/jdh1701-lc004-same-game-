import LC004.SeparatedPartitions
import LC004.RegionalCancellation

namespace LC004

/-- Split a carrier into an injected selected part and its exact complement. -/
noncomputable def splitComplementEquiv {α γ : Type*} (f : α → γ)
    (hf : Function.Injective f) (R : γ → Prop)
    (hR : ∀ x, R x ↔ ∀ a, f a ≠ x) : γ ≃ α ⊕ {x : γ // R x} := by
  classical
  refine (Equiv.ofBijective (Sum.elim f Subtype.val) ?_).symm
  constructor
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (hf h)
      | inr b => exact False.elim (((hR b.val).mp b.property) a h)
    | inr a =>
      cases y with
      | inl b => exact False.elim (((hR a.val).mp a.property) b h.symm)
      | inr b => exact congrArg Sum.inr (Subtype.ext h)
  · intro x
    by_cases hx : ∃ a, f a = x
    · obtain ⟨a,rfl⟩ := hx
      exact ⟨Sum.inl a,rfl⟩
    · exact ⟨Sum.inr ⟨x,(hR x).mpr (fun a ha => hx ⟨a,ha⟩)⟩,rfl⟩

theorem splitComplementEquiv_selected {α γ : Type*} (f : α → γ)
    (hf : Function.Injective f) (R : γ → Prop)
    (hR : ∀ x, R x ↔ ∀ a, f a ≠ x) (a : α) :
    splitComplementEquiv f hf R hR (f a) = Sum.inl a := by
  have he : (splitComplementEquiv f hf R hR).symm (Sum.inl a) = f a := rfl
  rw [← he,Equiv.apply_symm_apply]

theorem splitComplementEquiv_remainder {α γ : Type*} (f : α → γ)
    (hf : Function.Injective f) (R : γ → Prop)
    (hR : ∀ x, R x ↔ ∀ a, f a ≠ x) (x : {x : γ // R x}) :
    splitComplementEquiv f hf R hR x.val = Sum.inr x := by
  have he : (splitComplementEquiv f hf R hR).symm (Sum.inr x) = x.val := rfl
  rw [← he,Equiv.apply_symm_apply]

def quadPosition {n : Nat} (a b c d : Fin n) (i : Fin 4) : Fin n :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

theorem quadPosition_injective {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Function.Injective (quadPosition a b c d) := by
  intro i j h
  unfold quadPosition at h
  split_ifs at h <;> omega

theorem quadPosition_complement {n : Nat} (a b c d x : Fin n) :
    (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) ↔ ∀ i, quadPosition a b c d i ≠ x := by
  constructor
  · rintro ⟨ha,hb,hc,hd⟩ i
    unfold quadPosition
    split_ifs
    · exact Ne.symm ha
    · exact Ne.symm hb
    · exact Ne.symm hc
    · exact Ne.symm hd
  · intro h
    exact ⟨by simpa [quadPosition] using Ne.symm (h 0),
      by simpa [quadPosition] using Ne.symm (h 1),
      by simpa [quadPosition] using Ne.symm (h 2),
      by simpa [quadPosition] using Ne.symm (h 3)⟩

noncomputable def quadSplitEquiv {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Fin n ≃ Fin 4 ⊕ QuadRemainder a b c d :=
  splitComplementEquiv (quadPosition a b c d) (quadPosition_injective a b c d hab hbc hcd)
    (fun x => x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) (quadPosition_complement a b c d)

theorem quadSplitEquiv_selected {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (i : Fin 4) :
    quadSplitEquiv a b c d hab hbc hcd (quadPosition a b c d i) = Sum.inl i :=
  splitComplementEquiv_selected _ _ _ _ i

theorem quadSplitEquiv_remainder {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (x : QuadRemainder a b c d) :
    quadSplitEquiv a b c d hab hbc hcd x.val = Sum.inr x :=
  splitComplementEquiv_remainder _ _ _ _ x

/-- The regional branch family, now represented as full-board equivalence
relations on `Fin n`. Identification with all refining witnesses is separate. -/
noncomputable def fullBoardFourBlockFamily {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : List (Setoid (Fin n)) :=
  (regionalFourBlockFamily (remainderGapIndex a b c d)).map
    (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd))

theorem fullBoard_four_block_zero {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d))
    (hp : ¬p ≤ Setoid.ker (remainderGapIndex a b c d)) :
    collectedCoeff (unionTerms (· ⊔ ·) (fullBoardFourBlockFamily a b c d hab hbc hcd))
      (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd) ((⊤ : Setoid (Fin 4)),p)) = 0 := by
  rw [fullBoardFourBlockFamily,fullBoard_coefficient_transport]
  exact positional_regional_four_block_zero a b c d hab hbc hcd p hp

/-- Any full-board witness list with the same coverage below this target
inherits cancellation. The coverage premise is stated, not silently assumed. -/
theorem fullBoard_four_block_zero_of_coverage {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d))
    (hp : ¬p ≤ Setoid.ker (remainderGapIndex a b c d))
    (ws : List (Setoid (Fin n)))
    (hcover : ∀ x, x ≤ fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
        ((⊤ : Setoid (Fin 4)),p) →
      ((∃ r ∈ ws, r ≤ x) ↔
        (∃ r ∈ fullBoardFourBlockFamily a b c d hab hbc hcd, r ≤ x))) :
    collectedCoeff (unionTerms (· ⊔ ·) ws)
      (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd) ((⊤ : Setoid (Fin 4)),p)) = 0 := by
  classical
  letI := partitionFintype (Fin n)
  rw [collected_union_congr_below ws _ _ hcover]
  exact fullBoard_four_block_zero a b c d hab hbc hcd p hp

end LC004
