import LC004.RawEncoding
import LC004.RunEncoding

namespace LC004

/-- The two independently developed raw-to-run encoders in the repository
    agree on every input. This eliminates a modeling discrepancy before
    attempting the raw maximal-run vs compressed-run solvability bridge. -/
theorem encode_eq_encodeRuns (w : List Nat) :
    encode w = encodeRuns w := by
  induction w with
  | nil =>
      rfl
  | cons a xs ih =>
      simp only [encode, encodeRuns]
      rw [← ih]
      cases h : encode xs with
      | nil =>
          simp [pushColor]
      | cons x ys =>
          rcases x with ⟨c,b⟩
          by_cases hac : a = c
          · subst c
            simp [pushColor]
          · simp [pushColor, hac]

end LC004
