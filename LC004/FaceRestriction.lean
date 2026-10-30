import LC004.CertificateConstraintJoins

namespace LC004

/-- Restrict a color-pattern equivalence relation to a selected ordered
subset of positions. The map is allowed to select positions from different
geometric faces; no independence theorem is assumed. -/
def restrictColorPattern {n m : Nat} (p : ColorPattern n)
    (embed : Fin m → Fin n) : ColorPattern m :=
  Setoid.ker (fun i => Quotient.mk p (embed i))

/-- Restriction preserves the equivalence of two selected positions. -/
theorem restrictColorPattern_rel {n m : Nat}
    (p : ColorPattern n) (embed : Fin m → Fin n) (i j : Fin m) :
    restrictColorPattern p embed i j ↔ p (embed i) (embed j) := by
  change Quotient.mk p (embed i) = Quotient.mk p (embed j) ↔ _
  exact Quotient.eq

/-- Restriction commutes with pattern coarsening. -/
theorem restrictColorPattern_mono {n m : Nat}
    {p q : ColorPattern n} (hpq : p ≤ q) (embed : Fin m → Fin n) :
    restrictColorPattern p embed ≤ restrictColorPattern q embed := by
  intro i j hij
  exact (restrictColorPattern_rel q embed i j).mpr
    (hpq ((restrictColorPattern_rel p embed i j).mp hij))

#print axioms restrictColorPattern_rel
#print axioms restrictColorPattern_mono

end LC004
