import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace LC004
open scoped BigOperators

/-- Alternating face sum, including the empty face. For a nonempty complex this
is minus its reduced Euler characteristic. -/
def faceAlternatingSum {α : Type*} (F : Finset (Finset α)) : Int :=
  ∑ s ∈ F, (-1 : Int) ^ s.card

private def faceToggle {α : Type*} [DecidableEq α] (w : α) (s : Finset α) :=
  if w ∈ s then s.erase w else insert w s

private theorem faceToggle_twice {α : Type*} [DecidableEq α]
    (w : α) (s : Finset α) : faceToggle w (faceToggle w s) = s := by
  by_cases h : w ∈ s <;> simp [faceToggle, h]

private theorem faceToggle_ne {α : Type*} [DecidableEq α]
    (w : α) (s : Finset α) : faceToggle w s ≠ s := by
  by_cases h : w ∈ s
  · simpa [faceToggle, h] using Finset.erase_ne_self.mpr h
  · intro he
    have : w ∈ faceToggle w s := by simp [faceToggle, h]
    exact h (he ▸ this)

private theorem faceToggle_sign {α : Type*} [DecidableEq α]
    (w : α) (s : Finset α) :
    (-1 : Int) ^ s.card + (-1 : Int) ^ (faceToggle w s).card = 0 := by
  by_cases h : w ∈ s
  · have hc := Finset.card_erase_add_one h
    simp only [faceToggle, if_pos h]
    rw [← hc, pow_succ]
    ring
  · simp [faceToggle, h, Finset.card_insert_of_not_mem, pow_succ]

/-- Deleting a dominated vertex preserves the alternating face sum. The
assumptions isolate exactly the two closure facts needed for the involution:
deleting `w` preserves faces, and a face containing `v` can be extended by `w`.
This is an abstract finite-family theorem; it does not assert that the game
complex always has a dominated vertex. -/
theorem faceAlternatingSum_delete_dominated {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (v w : α) (hvw : v ≠ w)
    (herase : ∀ s ∈ F, s.erase w ∈ F)
    (hinsert : ∀ s ∈ F, v ∈ s → insert w s ∈ F) :
    faceAlternatingSum F = faceAlternatingSum (F.filter (v ∉ ·)) := by
  classical
  have hmem : ∀ s ∈ F.filter (v ∈ ·),
      faceToggle w s ∈ F.filter (v ∈ ·) := by
    intro s hs
    obtain ⟨hs, hv⟩ := Finset.mem_filter.mp hs
    by_cases hw : w ∈ s
    · simpa [faceToggle, hw, hvw, hv] using herase s hs
    · simpa [faceToggle, hw, hv] using hinsert s hs hv
  have hzero : (∑ s ∈ F.filter (v ∈ ·), (-1 : Int) ^ s.card) = 0 := by
    apply Finset.sum_involution (fun s _ => faceToggle w s)
    · intro s _; exact faceToggle_sign w s
    · intro s _ _; exact faceToggle_ne w s
    · exact hmem
    · intro s _; exact faceToggle_twice w s
  unfold faceAlternatingSum
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun s => v ∈ s)
    (fun s => (-1 : Int) ^ s.card)
  rw [hzero, zero_add] at hsplit
  exact hsplit.symm

/-- The downward closure of a finite family of facets. -/
def facetFaces {α : Type*} [DecidableEq α] (facets : Finset (Finset α)) :
    Finset (Finset α) := facets.biUnion Finset.powerset

theorem mem_facetFaces {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (s : Finset α) :
    s ∈ facetFaces facets ↔ ∃ f ∈ facets, s ⊆ f := by
  simp [facetFaces]

/-- The condition checked in the stored collapse certificates: every facet
containing `v` also contains a different vertex `w`. Deleting `v` from all
facets preserves the alternating sum of their downward closure. -/
theorem facetAlternatingSum_erase_dominated {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (v w : α) (hvw : v ≠ w)
    (hdom : ∀ f ∈ facets, v ∈ f → w ∈ f) :
    faceAlternatingSum (facetFaces facets) =
      faceAlternatingSum (facetFaces (facets.image (fun f => f.erase v))) := by
  classical
  have heq : (facetFaces facets).filter (v ∉ ·) =
      facetFaces (facets.image (fun f => f.erase v)) := by
    ext s
    simp only [Finset.mem_filter, mem_facetFaces, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, hsf⟩, hv⟩
      exact ⟨f.erase v, ⟨f, hf, rfl⟩, by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hx), hsf hx⟩⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, hs⟩
      exact ⟨⟨f, hf, fun x hx => (Finset.mem_erase.mp (hs hx)).2⟩,
        fun hv => Finset.not_mem_erase v f (hs hv)⟩
  rw [← heq]
  apply faceAlternatingSum_delete_dominated _ v w hvw
  · intro s hs
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces facets s).mp hs
    exact (mem_facetFaces facets _).mpr ⟨f, hf, Finset.erase_subset _ _ |>.trans hsf⟩
  · intro s hs hv
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces facets s).mp hs
    exact (mem_facetFaces facets _).mpr
      ⟨f, hf, Finset.insert_subset (hdom f hf (hsf hv)) hsf⟩

/-- A conservative majority operation, also called the dual discriminator. -/
def choiceMajority {α : Type*} [DecidableEq α] (x y z : α) : α :=
  if y = z then y else x

/-- Two-fan relations are closed under the coordinatewise majority operation. -/
theorem twoFan_closed_choiceMajority {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (x₁ x₂ x₃ : α) (y₁ y₂ y₃ : β)
    (h₁ : x₁ = a ∨ y₁ = b) (h₂ : x₂ = a ∨ y₂ = b)
    (h₃ : x₃ = a ∨ y₃ = b) :
    choiceMajority x₁ x₂ x₃ = a ∨ choiceMajority y₁ y₂ y₃ = b := by
  unfold choiceMajority
  split_ifs <;> aesop

/-- In a relation closed under this majority operation, a row containing two
distinct values contains every value occurring anywhere in the second column.
This is the key 0/1/All property for exact solution projections. -/
theorem choiceMajority_closed_row_all {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (hclosed : ∀ x₁ y₁ x₂ y₂ x₃ y₃, R x₁ y₁ → R x₂ y₂ → R x₃ y₃ →
      R (choiceMajority x₁ x₂ x₃) (choiceMajority y₁ y₂ y₃))
    (x u : α) (y z w : β) (hxy : R x y) (hxz : R x z)
    (hyz : y ≠ z) (huw : R u w) : R x w := by
  simpa [choiceMajority, hyz] using hclosed u w x y x z huw hxy hxz

#print axioms faceAlternatingSum_delete_dominated
#print axioms facetAlternatingSum_erase_dominated
#print axioms twoFan_closed_choiceMajority
#print axioms choiceMajority_closed_row_all
end LC004
