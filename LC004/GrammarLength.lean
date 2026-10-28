import Mathlib

namespace LC004

/-- Grammar of candidate Same Game winning words, with each production
    introducing two or three occurrences of the same color. -/
inductive Grammar (q : Nat) : List (Fin q) → Prop where
  | empty : Grammar q []
  | pair (a : Fin q) {u v : List (Fin q)} :
      Grammar q u → Grammar q v →
      Grammar q ([a] ++ u ++ [a] ++ v)
  | triple (a : Fin q) {u v w : List (Fin q)} :
      Grammar q u → Grammar q v → Grammar q w →
      Grammar q ([a] ++ u ++ [a] ++ v ++ [a] ++ w)

/-- A candidate winning word derived by this grammar cannot have length one. -/
theorem grammar_length_ne_one {q : Nat} {w : List (Fin q)}
    (h : Grammar q w) : w.length ≠ 1 := by
  cases h with
  | empty => simp
  | pair a hu hv =>
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | triple a hu hv hw =>
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

end LC004
