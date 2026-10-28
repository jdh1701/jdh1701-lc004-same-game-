import LC004.RawPrefixHeaviness

namespace LC004

/-- Adding any number of copies of the initial color to the front
    preserves solvability of the encoded Same Game position. -/
theorem encoded_repeated_head_solvable
    (a : Nat) (w : List Nat)
    (hw : Solvable Step (fun s => s = []) (encode (a :: w))) :
    ∀ k : Nat,
      Solvable Step (fun s => s = [])
        (encode (List.replicate k a ++ a :: w)) := by
  intro k
  induction k with
  | zero =>
      simpa using hw
  | succ k ih =>
      have h := encoded_duplicate_head_solvable a
        (List.replicate k a ++ w) (by
          simpa only [List.cons_append, List.append_assoc] using ih)
      simpa only [List.replicate_succ, List.cons_append] using h

end LC004
