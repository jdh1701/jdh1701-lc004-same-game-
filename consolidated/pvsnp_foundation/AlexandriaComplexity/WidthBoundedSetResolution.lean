import AlexandriaComplexity.SetResolution

namespace AlexandriaComplexity

/-!
Candidate formalization: every clause in a derivation has an explicit width
bound, including axioms and intermediate resolvents. For the generated
duplicate-free clauses, list length agrees with set cardinality.
Pinned Lean compilation and theorem audit are still required.
-/

inductive WidthBoundedSetResolutionDerivation
    (formula : CNF) (width : Nat) : Clause → Prop where
  | initial
      (clause : Clause)
      (present : containsClause clause formula = true)
      (bounded : clause.length ≤ width) :
      WidthBoundedSetResolutionDerivation formula width clause
  | resolve
      (pivot : Nat)
      (left right result : Clause)
      (leftHasPivot : containsLiteral (positiveLiteral pivot) left = true)
      (rightHasPivot : containsLiteral (negativeLiteral pivot) right = true)
      (sameResult : sameClause (generalResolvent pivot left right) result = true)
      (bounded : result.length ≤ width)
      (leftDerivation : WidthBoundedSetResolutionDerivation formula width left)
      (rightDerivation : WidthBoundedSetResolutionDerivation formula width right) :
      WidthBoundedSetResolutionDerivation formula width result

theorem width_bounded_set_resolution_forget
    (formula : CNF) (width : Nat) (clause : Clause)
    (derivation : WidthBoundedSetResolutionDerivation formula width clause) :
    SetResolutionDerivation formula clause := by
  induction derivation with
  | initial clause present bounded =>
      exact .initial clause present
  | resolve pivot left right result leftHasPivot rightHasPivot sameResult bounded
      leftDerivation rightDerivation leftProof rightProof =>
      exact .resolve pivot left right result leftHasPivot rightHasPivot sameResult
        leftProof rightProof

theorem width_bounded_set_resolution_refutation_unsat
    (formula : CNF) (width : Nat)
    (refutation : WidthBoundedSetResolutionDerivation formula width []) :
    ¬ ∃ assignment, evalCNF assignment formula = true :=
  set_resolution_refutation_unsat formula
    (width_bounded_set_resolution_forget formula width [] refutation)

end AlexandriaComplexity
