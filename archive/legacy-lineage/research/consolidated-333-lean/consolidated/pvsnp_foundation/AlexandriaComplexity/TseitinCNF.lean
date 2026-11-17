import AlexandriaComplexity.Tseitin

namespace AlexandriaComplexity

/-!
Explicit CNF encoding for a degree-3 Tseitin vertex constraint.

For incident edge variables x, y, z and charge c, the local constraint is
x XOR y XOR z = c. The CNF contains one clause for each falsifying local
assignment. This provides a semantic bridge from the parity formulation to
ordinary CNF semantics used by the Resolution layer.

This file does not yet prove a width or size lower bound.
-/

def literalForValue (index : Nat) (value : Bool) : Literal :=
  { index := index, positive := !value }

def parity3 (a b c : Bool) : Bool :=
  xorBool a (xorBool b c)

def parity3CNF (x y z : Nat) (charge : Bool) : CNF :=
  match charge with
  | false =>
      [
        [literalForValue x false, literalForValue y false, literalForValue z true],
        [literalForValue x false, literalForValue y true,  literalForValue z false],
        [literalForValue x true,  literalForValue y false, literalForValue z false],
        [literalForValue x true,  literalForValue y true,  literalForValue z true]
      ]
  | true =>
      [
        [literalForValue x false, literalForValue y false, literalForValue z false],
        [literalForValue x false, literalForValue y true,  literalForValue z true],
        [literalForValue x true,  literalForValue y false, literalForValue z true],
        [literalForValue x true,  literalForValue y true,  literalForValue z false]
      ]

theorem evalCNF_append
    (assignment : Assignment)
    (left right : CNF) :
    evalCNF assignment (left ++ right) =
      (evalCNF assignment left && evalCNF assignment right) := by
  induction left with
  | nil =>
      rfl
  | cons clause tail inductionHypothesis =>
      change
        (evalClause assignment clause &&
          evalCNF assignment (tail ++ right)) =
        ((evalClause assignment clause && evalCNF assignment tail) &&
          evalCNF assignment right)
      rw [inductionHypothesis]
      cases evalClause assignment clause <;>
        cases evalCNF assignment tail <;>
          cases evalCNF assignment right <;> rfl

theorem eval_parity3CNF
    (assignment : Assignment)
    (x y z : Nat)
    (charge : Bool) :
    evalCNF assignment (parity3CNF x y z charge) =
      (parity3 (assignment x) (assignment y) (assignment z) == charge) := by
  cases hx : assignment x <;>
    cases hy : assignment y <;>
      cases hz : assignment z <;>
        cases charge <;>
          simp only [parity3CNF, evalCNF, evalClause, evalLiteral, literalForValue,
            parity3, xorBool, hx, hy, hz, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, Bool.not_false, Bool.not_true,
            Bool.false_or, Bool.true_or, Bool.false_and, Bool.true_and] <;>
          decide

theorem parity3CNF_correct
    (assignment : Assignment)
    (x y z : Nat)
    (charge : Bool) :
    evalCNF assignment (parity3CNF x y z charge) = true ↔
      parity3 (assignment x) (assignment y) (assignment z) = charge := by
  rw [eval_parity3CNF]
  cases h : parity3 (assignment x) (assignment y) (assignment z) <;>
    cases charge <;>
      decide

/--
A concrete four-vertex, 3-regular Tseitin instance on K4.

Edge-variable indices:
0=e01, 1=e02, 2=e03, 3=e12, 4=e13, 5=e23.

Only vertex 0 carries charge true, so the total charge is odd.
-/
def k4OddTseitinCNF : CNF :=
  parity3CNF 0 1 2 true ++
  (parity3CNF 0 3 4 false ++
    (parity3CNF 1 3 5 false ++
      parity3CNF 2 4 5 false))

theorem k4OddTseitinCNF_unsat
    (assignment : Assignment) :
    evalCNF assignment k4OddTseitinCNF = false := by
  unfold k4OddTseitinCNF
  rw [evalCNF_append, evalCNF_append, evalCNF_append]
  rw [eval_parity3CNF, eval_parity3CNF, eval_parity3CNF, eval_parity3CNF]
  cases h0 : assignment 0 <;>
    cases h1 : assignment 1 <;>
      cases h2 : assignment 2 <;>
        cases h3 : assignment 3 <;>
          cases h4 : assignment 4 <;>
            cases h5 : assignment 5 <;>
              decide

end AlexandriaComplexity
