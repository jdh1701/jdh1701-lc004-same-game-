import AlexandriaComplexity.ResolutionProof

namespace AlexandriaComplexity

/-!
Arbitrary-position propositional Resolution over the existing list-clause
semantics.

`ResolutionProof` deliberately began with a head-pivot presentation.  This
module closes that representation gap: the selected positive and negative
pivot literals may occur anywhere in their parent clauses.  The resolvent
deletes the selected polarity from each parent and appends the remainders.

The membership premises keep the rule within ordinary Resolution.  The
soundness proof itself is semantic and does not claim completeness, a width
lower bound, or any consequence about P versus NP.
-/

def eraseLiteral (target : Literal) : Clause → Clause
  | [] => []
  | head :: tail =>
      if head = target then
        eraseLiteral target tail
      else
        head :: eraseLiteral target tail

theorem evalClause_erase_false
    (assignment : Assignment)
    (target : Literal)
    (clause : Clause)
    (targetFalse : evalLiteral assignment target = false)
    (clauseTrue : evalClause assignment clause = true) :
    evalClause assignment (eraseLiteral target clause) = true := by
  induction clause with
  | nil =>
      change false = true at clauseTrue
      contradiction
  | cons head tail inductionHypothesis =>
      by_cases equal : head = target
      · subst head
        rw [eraseLiteral]
        rw [if_pos rfl]
        change
          (evalLiteral assignment target || evalClause assignment tail) = true
          at clauseTrue
        rw [targetFalse] at clauseTrue
        exact inductionHypothesis clauseTrue
      · rw [eraseLiteral]
        rw [if_neg equal]
        change
          (evalLiteral assignment head || evalClause assignment tail) = true
          at clauseTrue
        change
          (evalLiteral assignment head ||
            evalClause assignment (eraseLiteral target tail)) = true
        cases headValue : evalLiteral assignment head with
        | false =>
            rw [headValue] at clauseTrue
            rw [Bool.false_or] at clauseTrue
            rw [Bool.false_or]
            exact inductionHypothesis clauseTrue
        | true =>
            rw [Bool.true_or]

def generalResolvent (pivot : Nat) (left right : Clause) : Clause :=
  eraseLiteral (positiveLiteral pivot) left ++
    eraseLiteral (negativeLiteral pivot) right

theorem general_resolution_step_sound
    (assignment : Assignment)
    (pivot : Nat)
    (left right : Clause)
    (leftTrue : evalClause assignment left = true)
    (rightTrue : evalClause assignment right = true) :
    evalClause assignment (generalResolvent pivot left right) = true := by
  cases pivotValue : assignment pivot with
  | false =>
      have positiveFalse :
          evalLiteral assignment (positiveLiteral pivot) = false := by
        change assignment pivot = false
        exact pivotValue
      have leftRemainderTrue :
          evalClause assignment
            (eraseLiteral (positiveLiteral pivot) left) = true :=
        evalClause_erase_false assignment (positiveLiteral pivot) left
          positiveFalse leftTrue
      unfold generalResolvent
      rw [evalClause_append, leftRemainderTrue]
      rfl
  | true =>
      have negativeFalse :
          evalLiteral assignment (negativeLiteral pivot) = false := by
        unfold evalLiteral negativeLiteral
        rw [pivotValue]
        rfl
      have rightRemainderTrue :
          evalClause assignment
            (eraseLiteral (negativeLiteral pivot) right) = true :=
        evalClause_erase_false assignment (negativeLiteral pivot) right
          negativeFalse rightTrue
      unfold generalResolvent
      rw [evalClause_append, rightRemainderTrue]
      cases evalClause assignment
        (eraseLiteral (positiveLiteral pivot) left) <;> rfl

inductive GeneralResolutionDerivation (formula : CNF) : Clause → Prop where
  | initial (clause : Clause) (present : clause ∈ formula) :
      GeneralResolutionDerivation formula clause
  | resolve
      (pivot : Nat)
      (left right : Clause)
      (leftHasPivot : positiveLiteral pivot ∈ left)
      (rightHasPivot : negativeLiteral pivot ∈ right)
      (leftDerivation : GeneralResolutionDerivation formula left)
      (rightDerivation : GeneralResolutionDerivation formula right) :
      GeneralResolutionDerivation formula (generalResolvent pivot left right)

theorem general_resolution_derivation_sound
    (assignment : Assignment)
    (formula : CNF)
    (clause : Clause)
    (formulaTrue : evalCNF assignment formula = true)
    (derivation : GeneralResolutionDerivation formula clause) :
    evalClause assignment clause = true := by
  induction derivation with
  | initial clause present =>
      exact evalCNF_member_true assignment formula clause formulaTrue present
  | resolve pivot left right leftHasPivot rightHasPivot
      leftDerivation rightDerivation leftSound rightSound =>
      exact general_resolution_step_sound assignment pivot left right
        leftSound rightSound

theorem general_resolution_refutation_unsat
    (formula : CNF)
    (refutation : GeneralResolutionDerivation formula []) :
    ¬ ∃ assignment, evalCNF assignment formula = true := by
  intro witness
  rcases witness with ⟨assignment, formulaTrue⟩
  have emptyTrue : evalClause assignment [] = true :=
    general_resolution_derivation_sound assignment formula [] formulaTrue refutation
  rw [empty_clause_is_false] at emptyTrue
  contradiction

end AlexandriaComplexity
