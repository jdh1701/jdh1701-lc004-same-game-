import LC004.RunState
import LC004.Normalized

namespace LC004

/-- Raw one-dimensional Same Game position: one color per cell. -/
abbrev RawState := List Nat

/-- Insert one raw cell at the left of an already compressed run state.
If it matches the first run, that run becomes heavy; otherwise a new
singleton run is created. -/
def pushColor (c : Nat) : RunState → RunState
  | [] => [(c, false)]
  | (d, b) :: xs =>
      if c = d then
        (d, true) :: xs
      else
        (c, false) :: (d, b) :: xs

/-- Compress a raw word into maximal color runs, remembering only whether
each run is a singleton or has size at least two. -/
def encode : RawState → RunState
  | [] => []
  | c :: cs => pushColor c (encode cs)

theorem normalized_pushColor
    (c : Nat) {s : RunState}
    (h : Normalized s) :
    Normalized (pushColor c s) := by
  cases s with
  | nil =>
      simp [pushColor, Normalized]
  | cons x xs =>
      rcases x with ⟨d, b⟩
      by_cases hcd : c = d
      · subst d
        cases xs with
        | nil =>
            simp [pushColor, Normalized]
        | cons y ys =>
            rcases y with ⟨e, be⟩
            simpa [pushColor, Normalized] using h
      · simpa [pushColor, hcd, Normalized] using And.intro hcd h

theorem encode_normalized (w : RawState) :
    Normalized (encode w) := by
  induction w with
  | nil =>
      simp [encode, Normalized]
  | cons c cs ih =>
      simpa [encode] using normalized_pushColor c ih

example : encode ([] : RawState) = [] := by rfl
example : encode [0] = [(0, false)] := by rfl
example : encode [0, 0] = [(0, true)] := by rfl
example :
    encode [0, 0, 1, 2, 2] =
      [(0, true), (1, false), (2, true)] := by
  rfl

end LC004
