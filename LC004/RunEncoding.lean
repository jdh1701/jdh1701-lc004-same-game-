import LC004.RunState
import LC004.Normalized

namespace LC004

/-- Raw one-dimensional Same Game words. -/
abbrev Word := List Nat

/-- Collapse a raw word into its run skeleton.  The Boolean records whether
the run has length at least two. -/
def encodeRuns : Word → RunState
  | [] => []
  | c :: xs =>
      match encodeRuns xs with
      | [] => [(c, false)]
      | (d, b) :: ys =>
          if c = d then
            (d, true) :: ys
          else
            (c, false) :: (d, b) :: ys

/-- Normalization depends only on run colors, not on the singleton/heavy bit. -/
theorem normalized_head_bit
    {c : Nat} {b e : Bool} {xs : RunState}
    (h : Normalized ((c,b)::xs)) :
    Normalized ((c,e)::xs) := by
  cases xs with
  | nil => simp [Normalized]
  | cons y ys =>
      rcases y with ⟨d,f⟩
      simpa [Normalized] using h

/-- The raw-word encoder always produces a normalized run state. -/
theorem normalized_encodeRuns : ∀ w : Word, Normalized (encodeRuns w) := by
  intro w
  induction w with
  | nil =>
      simp [encodeRuns, Normalized]
  | cons c xs ih =>
      rw [encodeRuns]
      cases henc : encodeRuns xs with
      | nil =>
          simp [henc, Normalized]
      | cons y ys =>
          rcases y with ⟨d,b⟩
          have ih' : Normalized ((d,b)::ys) := by
            simpa [henc] using ih
          by_cases hcd : c = d
          · subst d
            simpa [henc] using
              (normalized_head_bit (e := true) ih')
          · simpa [henc, hcd, Normalized] using
              (And.intro hcd ih')

end LC004
