import LC004.RawMaxSemanticsBridge

namespace LC004

/-- Construct words by inserting adjacent monochromatic pairs or triples
into any gap of a word already constructed. This representation remembers
a reverse deletion history; it is not yet a noncrossing partition of the
ORIGINAL positions. -/
inductive InsertionHistory {q : Nat} : List (Fin q) → Prop where
  | empty : InsertionHistory []
  | pair (left right : List (Fin q)) (a : Fin q) :
      InsertionHistory (left ++ right) →
      InsertionHistory (left ++ [a, a] ++ right)
  | triple (left right : List (Fin q)) (a : Fin q) :
      InsertionHistory (left ++ right) →
      InsertionHistory (left ++ [a, a, a] ++ right)

/-- Backward lifting along an auxiliary erasure path:
if the terminal word has an insertion-history certificate, then the
source word also has one. The endpoint remains arbitrary throughout
the induction, preventing dependent-index elaboration failures. -/
theorem insertion_history_backwards {q : Nat}
    {u v : List (Fin q)}
    (h : Erases u v) (hv : InsertionHistory v) :
    InsertionHistory u := by
  induction h with
  | refl _ => exact hv
  | next step rest ih =>
      cases step with
      | pair left right a =>
          exact InsertionHistory.pair left right a (ih hv)
      | triple left right a =>
          exact InsertionHistory.triple left right a (ih hv)

/-- Every successful pair/triple deletion history admits a
reverse contextual insertion history. -/
theorem erases_empty_to_insertion_history {q : Nat}
    {w : List (Fin q)} (h : Erases w []) :
    InsertionHistory w := by
  exact insertion_history_backwards h InsertionHistory.empty

/-- The reverse insertion history generates a finite auxiliary erasure
sequence, because each insertion reverses a legal contextual pair/triple
erasure. -/
theorem insertion_history_to_erases_empty {q : Nat}
    {w : List (Fin q)} (h : InsertionHistory w) :
    Erases w [] := by
  induction h with
  | empty =>
      exact Erases.refl []
  | pair left right a smaller ih =>
      exact Erases.next (SmallErase.pair left right a) ih
  | triple left right a smaller ih =>
      exact Erases.next (SmallErase.triple left right a) ih

theorem insertion_history_iff_erases_empty {q : Nat}
    (w : List (Fin q)) :
    InsertionHistory w ↔ Erases w [] := by
  exact ⟨insertion_history_to_erases_empty,
    erases_empty_to_insertion_history⟩

/-- This applies to real maximal-run-winning words via the existing
verified maximal-run to auxiliary-erasure direction. It does not prove
the converse. -/
theorem raw_max_win_to_insertion_history {q : Nat}
    {w : List (Fin q)} (h : LC004.RawMaxErases w []) :
    InsertionHistory w := by
  exact erases_empty_to_insertion_history
    (raw_max_win_to_aux_erases h)

#print axioms insertion_history_iff_erases_empty
#print axioms raw_max_win_to_insertion_history

end LC004
