import LC004.GrammarLength

namespace LC004

/-- Grammar membership is invariant under a permutation of color names.
This is the mathematical foundation for color-orbit quotienting, not
a proof of the particular Python quotient implementation. -/
theorem grammar_color_equiv_iff {q : Nat}
    (f : Fin q ≃ Fin q) (w : List (Fin q)) :
    Grammar q (w.map f) ↔ Grammar q w := by
  constructor
  · intro h
    have hback : Grammar q ((w.map f).map f.symm) :=
      grammar_map f.symm h
    simpa using hback
  · intro h
    exact grammar_map f h

end LC004
