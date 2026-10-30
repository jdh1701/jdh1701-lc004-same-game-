import LC004.LocalCertificateCatalogues
import LC004.ChoiceRelationClassification

namespace LC004

/-- Original mixed pattern with class sizes five and six. -/
def mixed56BaseColor : Fin 11 → Fin 2 := ![0,0,1,0,0,1,1,0,1,1,1]
def mixed56Pattern : ColorPattern 11 := Setoid.ker mixed56BaseColor

def mixed56LeftFn : Fin 5 → Fin 11 := ![0,1,3,4,7]
def mixed56RightFn : Fin 6 → Fin 11 := ![2,5,6,8,9,10]

theorem mixed56Left_mono : StrictMono mixed56LeftFn := by decide +kernel
theorem mixed56Right_mono : StrictMono mixed56RightFn := by decide +kernel

def mixed56Left : Fin 5 ↪o Fin 11 := OrderEmbedding.ofStrictMono mixed56LeftFn mixed56Left_mono
def mixed56Right : Fin 6 ↪o Fin 11 := OrderEmbedding.ofStrictMono mixed56RightFn mixed56Right_mono

def mixed56LeftRank : Fin 11 → Fin 5 := ![0,1,0,2,3,0,0,4,0,0,0]
def mixed56RightRank : Fin 11 → Fin 6 := ![0,0,0,0,0,1,2,0,3,4,5]

def mixed56Color (s : Fin 5) (t : Fin 8) (x : Fin 11) : Fin 11 :=
  if mixed56BaseColor x = 0 then
    ⟨(localNC5Color s (mixed56LeftRank x)).val,by omega⟩
  else ⟨5 + (localNC6Color t (mixed56RightRank x)).val,by omega⟩

def mixed56Encoded (s : Fin 5) (t : Fin 8) : ColorPattern 11 := Setoid.ker (mixed56Color s t)

theorem mixed56_cover : ∀ x : Fin 11,
    (∃ u, mixed56Left u = x) ∨ (∃ v, mixed56Right v = x) := by decide +kernel

theorem mixed56_left_saturated : ∀ u : Fin 5, ∀ x : Fin 11,
    mixed56BaseColor (mixed56Left u) = mixed56BaseColor x → ∃ v, mixed56Left v = x := by
  decide +kernel

theorem mixed56_right_saturated : ∀ u : Fin 6, ∀ x : Fin 11,
    mixed56BaseColor (mixed56Right u) = mixed56BaseColor x → ∃ v, mixed56Right v = x := by
  decide +kernel

theorem mixed56_cross_different : ∀ u : Fin 5, ∀ v : Fin 6,
    mixed56BaseColor (mixed56Left u) ≠ mixed56BaseColor (mixed56Right v) := by decide +kernel

theorem mixed56_encoded_left : ∀ s : Fin 5, ∀ t : Fin 8, ∀ u v : Fin 5,
    mixed56Color s t (mixed56Left u) = mixed56Color s t (mixed56Left v) ↔
      localNC5Color s u = localNC5Color s v := by decide +kernel

theorem mixed56_encoded_right : ∀ s : Fin 5, ∀ t : Fin 8, ∀ u v : Fin 6,
    mixed56Color s t (mixed56Right u) = mixed56Color s t (mixed56Right v) ↔
      localNC6Color t u = localNC6Color t v := by decide +kernel

theorem mixed56_encoded_cross : ∀ s : Fin 5, ∀ t : Fin 8, ∀ u : Fin 5, ∀ v : Fin 6,
    mixed56Color s t (mixed56Left u) ≠ mixed56Color s t (mixed56Right v) := by decide +kernel

/-- This relation is computed directly from original position labels. -/
def Mixed56Compatible (s : Fin 5) (t : Fin 8) : Prop := NoncrossingColor (mixed56Color s t)

theorem mixed56_compatible_iff : ∀ s : Fin 5, ∀ t : Fin 8,
    Mixed56Compatible s t ↔ (s = 2 ∧ t = 4) ∨ (s = 2 ∧ t = 6) ∨ (s = 1 ∧ t = 0) := by
  unfold Mixed56Compatible NoncrossingColor
  decide +kernel

/-- The all-five majority-closure mechanism already fails on an actual (5,6)
position pattern. The three inputs are valid original noncrossing certificates. -/
theorem mixed56_not_majority_closed : ¬ ChoiceRelationClosed Mixed56Compatible := by
  intro h
  have hb := h 1 0 2 4 2 6
    ((mixed56_compatible_iff 1 0).mpr (Or.inr (Or.inr ⟨rfl,rfl⟩)))
    ((mixed56_compatible_iff 2 4).mpr (Or.inl ⟨rfl,rfl⟩))
    ((mixed56_compatible_iff 2 6).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
  have hn : ¬ Mixed56Compatible 2 0 := by rw [mixed56_compatible_iff]; decide
  exact hn (by simpa [choiceMajority] using hb)

/-- Coveredness survives in this counterexample: it is specifically majority
closure, rather than the two-fan cover, that fails. -/
theorem mixed56_covered : ∀ s t, Mixed56Compatible s t → s = 2 ∨ t = 0 := by
  intro s t h
  rcases (mixed56_compatible_iff s t).mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem mixed56_profile :
    (Finset.univ.filter (fun i => mixed56BaseColor i = 0)).card = 5 ∧
    (Finset.univ.filter (fun i => mixed56BaseColor i = 1)).card = 6 := by decide +kernel

theorem mixed56_pattern_crosses : ¬ PatternNoncrossing mixed56Pattern := by
  intro h
  have hh := h 1 2 3 5 (by decide) (by decide) (by decide) rfl rfl
  change mixed56BaseColor 1 = mixed56BaseColor 2 at hh
  have hn : mixed56BaseColor 1 ≠ mixed56BaseColor 2 := by decide
  exact hn hh

#print axioms mixed56_not_majority_closed
#print axioms mixed56_pattern_crosses
end LC004
