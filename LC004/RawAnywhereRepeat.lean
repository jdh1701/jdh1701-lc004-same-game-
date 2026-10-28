import LC004.RawAnywhereHeaviness

namespace LC004

/-- Once a run already contains a given cell, inserting any finite
number of further copies of that color immediately after it preserves
solvability in the encoded run-state game, at any raw-word position. -/
theorem encoded_repeat_anywhere_solvable
    (pre : List Nat) (a : Nat) (suffix : List Nat)
    (h : Solvable Step (fun s => s = [])
      (encode (pre ++ a :: suffix))) :
    ∀ k : Nat, Solvable Step (fun s => s = [])
      (encode (pre ++ a :: List.replicate k a ++ suffix)) := by
  intro k
  induction k with
  | zero =>
      simpa using h
  | succ k ih =>
      have hd := encoded_duplicate_anywhere_solvable
        pre a (List.replicate k a ++ suffix) ih
      simpa only [List.replicate_succ, List.cons_append] using hd

end LC004
