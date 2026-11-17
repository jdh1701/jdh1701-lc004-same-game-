import LC004.CertificateConstraintJoins

namespace LC004

/-- Three simultaneous equality constraints are admitted precisely when
each individual constraint is admitted. This is an algebraic prerequisite,
not the geometric Face Lemma. -/
theorem constraintIndicator_triple_join {n : Nat}
    (p q s r : ColorPattern n) :
    constraintIndicator ((p ⊔ q) ⊔ s) r =
      constraintIndicator p r * constraintIndicator q r *
        constraintIndicator s r := by
  rw [constraintIndicator_join, constraintIndicator_join]

/-- Adding a constraint already implied by the ambient pattern changes
no indicator score. -/
theorem constraintIndicator_join_of_le {n : Nat}
    (p q r : ColorPattern n) (hq : q ≤ r) :
    constraintIndicator (p ⊔ q) r = constraintIndicator p r := by
  rw [constraintIndicator_join]
  simp [constraintIndicator, hq]

#print axioms constraintIndicator_triple_join
#print axioms constraintIndicator_join_of_le

end LC004
