import Std

namespace AlexandriaComplexity.LocalParity

/-!
Candidate finite algebra kernels only. These statements do not formalize
graphs, clauses, subsumption, or the general Resolution lower bound.
`decide` requests kernel-reduced finite checking, not native evaluation.
Actual pinned compilation remains a separate obligation.
-/

def xor3 (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c

def xor4 (a b c d : Bool) : Bool := Bool.xor (xor3 a b c) d

theorem adjacent_vertices_wrong_parity :
    ∀ (t a b d f cu cv : Bool),
      xor3 t a b = !cu →
      xor3 (!t) d f = !cv →
      xor4 a b d f = !(Bool.xor cu cv) := by
  decide

theorem contained_vertex_wrong_parity :
    ∀ (e a b d f cu cv : Bool),
      xor3 e a b = !cv →
      xor4 (!a) b d f = !(Bool.xor cv cu) →
      xor3 e d f = !cu := by
  decide

end AlexandriaComplexity.LocalParity
