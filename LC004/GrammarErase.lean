import LC004.GrammarLength

namespace LC004

/-- Contextual deletion of two or three adjacent cells of the same color. -/
inductive SmallErase {q : Nat} : List (Fin q) → List (Fin q) → Prop where
  | pair (left right : List (Fin q)) (a : Fin q) :
      SmallErase (left ++ [a, a] ++ right) (left ++ right)
  | triple (left right : List (Fin q)) (a : Fin q) :
      SmallErase (left ++ [a, a, a] ++ right) (left ++ right)

/-- Reflexive transitive closure of contextual pair/triple deletion. -/
inductive Erases {q : Nat} : List (Fin q) → List (Fin q) → Prop where
  | refl (w : List (Fin q)) : Erases w w
  | next {u v w : List (Fin q)} :
      SmallErase u v → Erases v w → Erases u w

theorem erases_trans {q : Nat} {u v w : List (Fin q)}
    (h : Erases u v) (k : Erases v w) : Erases u w := by
  induction h with
  | refl _ => exact k
  | next step rest ih => exact Erases.next step (ih k)

theorem smallErase_context {q : Nat}
    {u v : List (Fin q)} (h : SmallErase u v)
    (left right : List (Fin q)) :
    SmallErase (left ++ u ++ right) (left ++ v ++ right) := by
  cases h with
  | pair l r a =>
      simpa only [List.append_assoc] using
        (SmallErase.pair (left ++ l) (r ++ right) a)
  | triple l r a =>
      simpa only [List.append_assoc] using
        (SmallErase.triple (left ++ l) (r ++ right) a)

theorem erases_context {q : Nat}
    {u v : List (Fin q)} (h : Erases u v)
    (left right : List (Fin q)) :
    Erases (left ++ u ++ right) (left ++ v ++ right) := by
  induction h with
  | refl _ => exact Erases.refl _
  | next step rest ih =>
      exact Erases.next (smallErase_context step left right) ih

private theorem erase_pair_composition {q : Nat}
    (a : Fin q) {u v : List (Fin q)}
    (hu : Erases u []) (hv : Erases v []) :
    Erases ([a] ++ u ++ [a] ++ v) [] := by
  have h1 : Erases ([a] ++ u ++ [a] ++ v) ([a, a] ++ v) := by
    simpa only [List.append_assoc, List.nil_append] using
      (erases_context hu [a] ([a] ++ v))
  have h2 : Erases ([a, a] ++ v) v := by
    simpa using (Erases.next (SmallErase.pair [] v a) (Erases.refl v))
  exact erases_trans h1 (erases_trans h2 hv)

private theorem erase_triple_composition {q : Nat}
    (a : Fin q) {u v w : List (Fin q)}
    (hu : Erases u []) (hv : Erases v []) (hw : Erases w []) :
    Erases ([a] ++ u ++ [a] ++ v ++ [a] ++ w) [] := by
  have h1 : Erases ([a] ++ u ++ [a] ++ v ++ [a] ++ w)
      ([a, a] ++ v ++ [a] ++ w) := by
    simpa only [List.append_assoc, List.nil_append] using
      (erases_context hu [a] ([a] ++ v ++ [a] ++ w))
  have h2 : Erases ([a, a] ++ v ++ [a] ++ w)
      ([a, a, a] ++ w) := by
    simpa only [List.append_assoc, List.nil_append] using
      (erases_context hv [a, a] ([a] ++ w))
  have h3 : Erases ([a, a, a] ++ w) w := by
    simpa using (Erases.next (SmallErase.triple [] w a) (Erases.refl w))
  exact erases_trans h1 (erases_trans h2 (erases_trans h3 hw))

/-- Every grammar-derived word can be erased through contextual
    adjacent pair/triple deletions. This does not yet establish the
    equivalence with maximal-run Same Game moves. -/
theorem grammar_erases_empty {q : Nat} {w : List (Fin q)}
    (h : Grammar q w) : Erases w [] := by
  induction h with
  | empty => exact Erases.refl []
  | pair a hu hv ihu ihv =>
      exact erase_pair_composition a ihu ihv
  | triple a hu hv hw ihu ihv ihw =>
      exact erase_triple_composition a ihu ihv ihw

end LC004
