import AlexandriaComplexity.CNF

namespace AlexandriaComplexity

/-!
A first proof-complexity milestone: semantic soundness of one propositional
Resolution inference. This theorem is deliberately restricted. It says that
if an assignment satisfies both parent clauses containing opposite polarities
of a pivot variable, then it satisfies the resolvent formed by deleting the
pivot literals and concatenating the remaining literals.

It does not state a Resolution lower bound, a general proof-system lower bound,
or any consequence about P versus NP.
-/

def positiveLiteral (index : Nat) : Literal :=
  { index := index, positive := true }

def negativeLiteral (index : Nat) : Literal :=
  { index := index, positive := false }

def resolvent (left right : Clause) : Clause :=
  left ++ right

theorem evalClause_append (assignment : Assignment) (left right : Clause) :
    evalClause assignment (left ++ right) =
      (evalClause assignment left || evalClause assignment right) := by
  induction left with
  | nil =>
      rfl
  | cons literal tail inductionHypothesis =>
      change
        (evalLiteral assignment literal || evalClause assignment (tail ++ right)) =
          ((evalLiteral assignment literal || evalClause assignment tail) ||
            evalClause assignment right)
      rw [inductionHypothesis]
      cases evalLiteral assignment literal <;>
        cases evalClause assignment tail <;>
          cases evalClause assignment right <;> rfl

theorem resolution_step_sound
    (assignment : Assignment)
    (pivot : Nat)
    (left right : Clause)
    (leftSatisfied :
      evalClause assignment (positiveLiteral pivot :: left) = true)
    (rightSatisfied :
      evalClause assignment (negativeLiteral pivot :: right) = true) :
    evalClause assignment (resolvent left right) = true := by
  cases pivotValue : assignment pivot with
  | false =>
      change (assignment pivot || evalClause assignment left) = true at leftSatisfied
      rw [pivotValue] at leftSatisfied
      change evalClause assignment left = true at leftSatisfied
      rw [resolvent, evalClause_append, leftSatisfied]
      rfl
  | true =>
      change ((!assignment pivot) || evalClause assignment right) = true at rightSatisfied
      rw [pivotValue] at rightSatisfied
      change evalClause assignment right = true at rightSatisfied
      rw [resolvent, evalClause_append, rightSatisfied]
      cases evalClause assignment left <;> rfl

end AlexandriaComplexity
