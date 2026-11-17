import AlexandriaComplexity.WidthBoundedSetResolution

namespace AlexandriaComplexity

/-!
Generic lower-bound principle. This candidate theorem is CONDITIONAL on
explicit initial-clause, closure, and empty-exclusion obligations. It does not
assert that the concrete Python certificates discharge these obligations.
-/

structure WidthClosedInvariant (formula : CNF) (width : Nat) where
  holds : Clause → Prop
  initial : ∀ clause,
    containsClause clause formula = true → clause.length ≤ width → holds clause
  closed : ∀ pivot left right result,
    containsLiteral (positiveLiteral pivot) left = true →
    containsLiteral (negativeLiteral pivot) right = true →
    sameClause (generalResolvent pivot left right) result = true →
    result.length ≤ width → holds left → holds right → holds result
  excludesEmpty : ¬ holds []

theorem width_closed_invariant_preserved
    (formula : CNF) (width : Nat)
    (invariant : WidthClosedInvariant formula width)
    (clause : Clause)
    (derivation : WidthBoundedSetResolutionDerivation formula width clause) :
    invariant.holds clause := by
  induction derivation with
  | initial clause present bounded =>
      exact invariant.initial clause present bounded
  | resolve pivot left right result leftHasPivot rightHasPivot sameResult bounded
      leftDerivation rightDerivation leftHolds rightHolds =>
      exact invariant.closed pivot left right result leftHasPivot rightHasPivot
        sameResult bounded leftHolds rightHolds

theorem width_closed_invariant_no_refutation
    (formula : CNF) (width : Nat)
    (invariant : WidthClosedInvariant formula width) :
    ¬ WidthBoundedSetResolutionDerivation formula width [] := by
  intro refutation
  exact invariant.excludesEmpty
    (width_closed_invariant_preserved formula width invariant [] refutation)

end AlexandriaComplexity
