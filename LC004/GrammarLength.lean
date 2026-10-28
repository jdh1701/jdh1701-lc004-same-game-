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

/-- Renaming colors preserves membership in the candidate grammar. -/
theorem grammar_map {q r : Nat} (f : Fin q → Fin r)
    {w : List (Fin q)} (h : Grammar q w) :
    Grammar r (w.map f) := by
  induction h with
  | empty =>
      simpa using (Grammar.empty : Grammar r [])
  | pair a hu hv ihu ihv =>
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        (Grammar.pair (f a) ihu ihv)
  | triple a hu hv hw ihu ihv ihw =>
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        (Grammar.triple (f a) ihu ihv ihw)

/-- A grammar derivation is either empty or at least two positions long. -/
theorem grammar_empty_or_length_ge_two {q : Nat}
    {w : List (Fin q)} (h : Grammar q w) :
    w = [] ∨ 2 ≤ w.length := by
  cases h with
  | empty => exact Or.inl rfl
  | pair a hu hv =>
      right
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | triple a hu hv hw =>
      right
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Concatenation preserves the candidate winning-word grammar.
    This is a key compositional lemma for a later soundness theorem. -/
theorem grammar_append {q : Nat} {u v : List (Fin q)}
    (hu : Grammar q u) (hv : Grammar q v) :
    Grammar q (u ++ v) := by
  induction hu generalizing v with
  | empty =>
      simpa using hv
  | pair a hu₁ hu₂ ih₁ ih₂ =>
      simpa only [List.append_assoc] using
        (Grammar.pair a hu₁ (ih₂ hv))
  | triple a hu₁ hu₂ hu₃ ih₁ ih₂ ih₃ =>
      simpa only [List.append_assoc] using
        (Grammar.triple a hu₁ hu₂ (ih₃ hv))

end LC004
