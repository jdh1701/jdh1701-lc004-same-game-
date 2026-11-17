import AlexandriaComplexity.TseitinCNF

namespace AlexandriaComplexity

/-!
A minimal Resolution derivation system over the CNF semantics already used by
Alexandria. Initial clauses may be used directly. The only inference rule is
the semantic Resolution step already proved sound in Resolution.lean.

This layer proves that every derived clause is satisfied by every assignment
that satisfies the initial CNF, and therefore that deriving the empty clause
certifies unsatisfiability.
-/

inductive ResolutionDerivation (formula : CNF) : Clause → Prop where
  | initial (clause : Clause) (present : clause ∈ formula) :
      ResolutionDerivation formula clause
  | resolve
      (pivot : Nat)
      (left right : Clause)
      (leftDerivation :
        ResolutionDerivation formula (positiveLiteral pivot :: left))
      (rightDerivation :
        ResolutionDerivation formula (negativeLiteral pivot :: right)) :
      ResolutionDerivation formula (resolvent left right)

theorem evalCNF_member_true
    (assignment : Assignment)
    (formula : CNF)
    (clause : Clause)
    (formulaTrue : evalCNF assignment formula = true)
    (present : clause ∈ formula) :
    evalClause assignment clause = true := by
  induction formula with
  | nil =>
      cases present
  | cons head tail inductionHypothesis =>
      change
        (evalClause assignment head && evalCNF assignment tail) = true
        at formulaTrue
      cases hHead : evalClause assignment head with
      | false =>
          rw [hHead] at formulaTrue
          contradiction
      | true =>
          rw [hHead] at formulaTrue
          cases present with
          | head =>
              exact hHead
          | tail _ tailPresent =>
              exact inductionHypothesis formulaTrue tailPresent

theorem resolution_derivation_sound
    (assignment : Assignment)
    (formula : CNF)
    (clause : Clause)
    (formulaTrue : evalCNF assignment formula = true)
    (derivation : ResolutionDerivation formula clause) :
    evalClause assignment clause = true := by
  induction derivation with
  | initial clause present =>
      exact evalCNF_member_true assignment formula clause formulaTrue present
  | resolve pivot left right leftDerivation rightDerivation leftSound rightSound =>
      exact resolution_step_sound assignment pivot left right leftSound rightSound

theorem resolution_refutation_unsat
    (formula : CNF)
    (refutation : ResolutionDerivation formula []) :
    ¬ ∃ assignment, evalCNF assignment formula = true := by
  intro witness
  rcases witness with ⟨assignment, formulaTrue⟩
  have emptyTrue :
      evalClause assignment [] = true :=
    resolution_derivation_sound assignment formula [] formulaTrue refutation
  rw [empty_clause_is_false] at emptyTrue
  contradiction

end AlexandriaComplexity
