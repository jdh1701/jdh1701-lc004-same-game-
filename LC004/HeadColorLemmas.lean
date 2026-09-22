import LC004.IndexedMove
import LC004.RunState

namespace LC004

def headColor? (s : RunState) : Option Nat :=
  s.head?.map Prod.fst

theorem indexedStep_nonzero_headColor
    {s t : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : IndexedStep s i t) :
    headColor? s = headColor? t := by
  cases h with
  | @noMerge pre post c hboundary =>
      have hpre : pre ≠ [] := by
        intro hp
        subst pre
        simp at hi
      cases pre with
      | nil => contradiction
      | cons x xs =>
          simp [headColor?]
  | @merge pre post c d bp bq =>
      cases pre with
      | nil =>
          simp [headColor?]
      | cons x xs =>
          simp [headColor?]

theorem heavier_headColor
    {s t : RunState}
    (h : Heavier s t) :
    headColor? s = headColor? t := by
  cases s with
  | nil =>
      cases t <;> simp [Heavier, headColor?] at h ⊢
  | cons x xs =>
      cases t with
      | nil =>
          simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp [Heavier] at h
          simp [headColor?, h.1]

end LC004
