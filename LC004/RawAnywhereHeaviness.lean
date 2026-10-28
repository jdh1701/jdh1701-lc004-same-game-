import LC004.RawPrefixHeaviness

namespace LC004

/-- Prefixing identical raw cells respects the run-state heaviness relation. -/
theorem heavier_pushColor (c : Nat)
    {s t : RunState} (h : Heavier s t) :
    Heavier (pushColor c s) (pushColor c t) := by
  cases s with
  | nil =>
      cases t with
      | nil => simp [pushColor, Heavier]
      | cons y ys => simp [Heavier] at h
  | cons x xs =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨d,b⟩
          rcases y with ⟨e,f⟩
          change d = e ∧ (b → f) ∧ Heavier xs ys at h
          rcases h with ⟨rfl,hbf,hrest⟩
          by_cases hc : c = d
          · subst d
            simp [pushColor, Heavier, hrest]
          · simp [pushColor, hc, Heavier, hbf, hrest]

/-- The same prefix can be added to any related raw encodings. -/
theorem heavier_encode_prefix
    (prefix : List Nat) {u v : List Nat}
    (h : Heavier (encode u) (encode v)) :
    Heavier (encode (prefix ++ u)) (encode (prefix ++ v)) := by
  induction prefix with
  | nil => simpa using h
  | cons c cs ih =>
      simpa [encode, List.cons_append] using
        (heavier_pushColor c (ih h))

/-- Duplication at any position in the raw word makes its run
encoding at least as heavy without changing the run-color skeleton. -/
theorem encode_duplicate_anywhere_heavier
    (prefix : List Nat) (a : Nat) (suffix : List Nat) :
    Heavier (encode (prefix ++ a :: suffix))
      (encode (prefix ++ a :: a :: suffix)) := by
  exact heavier_encode_prefix prefix
    (encode_duplicate_head_heavier a suffix)

/-- Solvability in the compressed run model survives duplication of
a raw cell at an arbitrary position. -/
theorem encoded_duplicate_anywhere_solvable
    (prefix : List Nat) (a : Nat) (suffix : List Nat)
    (h : Solvable Step (fun s => s = [])
      (encode (prefix ++ a :: suffix))) :
    Solvable Step (fun s => s = [])
      (encode (prefix ++ a :: a :: suffix)) := by
  exact sameGame_solvable_mono_full
    (encode_duplicate_anywhere_heavier prefix a suffix) h

end LC004
