import LC004.JoinRigidBlocks

namespace LC004
open scoped Classical

/-- Own attempt (Claude, 2026-10-30): package `join_small_class_no_cross` (R2)
as a clean corollary stated in terms of an ordinary crossing `a < b < c < d`,
`x a c`, `x b d`, `¬ x a b`, rather than R2's own raw interior/exterior
hypothesis shape. R2 itself only concludes `False` from a specific witness
`u,v,w,z`; this shows that witness is always available from any genuine
crossing, so a class crossed inside a join of pair/triple certificates can
never have size <= 3. This does not yet address the size-4 case (that needs
`winningJoinCoefficient_crossed_four_zero` plus a separate argument for
naming the crossed class's own sorted four elements, which this file does
not attempt) -- see the 2026-10-30 WORKBOARD entry for the scoped remainder. -/
theorem join_crossed_class_card_ge_four {n : Nat} {F : Finset (ColorPattern n)}
    {x : ColorPattern n} (hF : ∀ c ∈ F, CertificateConstraint c)
    (hle : ∀ c ∈ F, c ≤ x)
    (hmin : ∀ y : ColorPattern n, (∀ c ∈ F, c ≤ y) → x ≤ y)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : x a c) (hbd : x b d) (hnab : ¬ x a b) :
    4 ≤ (patternClassPositions x a).card := by
  by_contra hcard
  push_neg at hcard
  have hsmall : (patternClassPositions x a).card ≤ 3 := by omega
  -- `¬ x a d` follows from `¬ x a b` and `x b d` alone, with no case split:
  -- if `x a d` held, transitivity with `x b d` would force `x a b`.
  have hnad : ¬ x a d := fun had => hnab (x.symm' (x.trans' hbd (x.symm' had)))
  have hac' : a < c := hab.trans hbc
  have hz : ¬ (a < d ∧ d < c) := fun h => absurd h.2 (not_lt.mpr hcd.le)
  exact join_small_class_no_cross hF hle hmin hac' hac hsmall hbd hab hbc hz hnad

#print axioms join_crossed_class_card_ge_four
end LC004
