import LC004.RawEncoding
import LC004.FullSimulation

namespace LC004

/-- Doubling an initial raw cell does not change the encoded run-color
skeleton, and only increases the heaviness flag of its first run. -/
theorem encode_duplicate_head_heavier
    (a : Nat) (w : List Nat) :
    Heavier (encode (a :: w)) (encode (a :: a :: w)) := by
  simp only [encode]
  cases h : encode w with
  | nil =>
      simp [pushColor, Heavier]
  | cons x xs =>
      rcases x with ⟨c, heavy⟩
      by_cases hac : a = c
      · subst c
        simp [pushColor, heavier_refl]
      · simp [pushColor, hac, Heavier, heavier_refl]

/-- Encoded Same Game solvability is preserved when the first raw
cell is duplicated. This is a genuine consequence of the established
full run-state simulation theorem, not an assertion about arbitrary
insertion gaps yet. -/
theorem encoded_duplicate_head_solvable
    (a : Nat) (w : List Nat)
    (hw : Solvable Step (fun s => s = []) (encode (a :: w))) :
    Solvable Step (fun s => s = []) (encode (a :: a :: w)) := by
  exact sameGame_solvable_mono_full
    (encode_duplicate_head_heavier a w) hw

end LC004
