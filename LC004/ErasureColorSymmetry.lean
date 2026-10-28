import LC004.GrammarErase

namespace LC004

/-- Contextual pair/triple erasure commutes with global color renaming. -/
theorem smallErase_color_map {q r : Nat} (f : Fin q → Fin r)
    {u v : List (Fin q)} (h : SmallErase u v) :
    SmallErase (u.map f) (v.map f) := by
  cases h with
  | pair left right a =>
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        (SmallErase.pair (left.map f) (right.map f) (f a))
  | triple left right a =>
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        (SmallErase.triple (left.map f) (right.map f) (f a))

/-- All finite contextual pair/triple erasure paths are equivariant
    under color renaming. The map does not have to be injective. -/
theorem erases_color_map {q r : Nat} (f : Fin q → Fin r)
    {u v : List (Fin q)} (h : Erases u v) :
    Erases (u.map f) (v.map f) := by
  induction h with
  | refl w =>
      exact Erases.refl _
  | next step rest ih =>
      exact Erases.next (smallErase_color_map f step) ih

/-- Pair/triple erasability is unchanged by a color permutation. -/
theorem erases_color_equiv_iff {q : Nat} (f : Fin q ≃ Fin q)
    (u v : List (Fin q)) :
    Erases (u.map f) (v.map f) ↔ Erases u v := by
  constructor
  · intro h
    have hb := erases_color_map f.symm h
    simpa using hb
  · intro h
    exact erases_color_map f h

end LC004
