import LC004.FaceRestriction

namespace LC004

/-- A restricted equivalence relation cannot identify positions unless
the original relation identifies their images. -/
theorem restrictColorPattern_iff {n m : Nat}
    (p : ColorPattern n) (e : Fin m → Fin n) (i j : Fin m) :
    (restrictColorPattern p e) i j ↔ p (e i) (e j) :=
  restrictColorPattern_rel p e i j

/-- The join of restricted patterns always lies below the restriction
of their join. The reverse inequality is the genuine face-boundary
obligation, and fails without additional hypotheses. -/
theorem join_restrictions_le_restrict_join {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n) :
    restrictColorPattern p e ⊔ restrictColorPattern q e ≤
      restrictColorPattern (p ⊔ q) e := by
  apply sup_le
  · exact restrictColorPattern_mono le_sup_left e
  · exact restrictColorPattern_mono le_sup_right e

/-- The exact remaining proof obligation for face-local join equality:
every equivalence in the restricted global join must be witnessed by
the join of the face-local restrictions. -/
theorem restrict_join_eq_of_no_external_bridge {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n)
    (hbridge : restrictColorPattern (p ⊔ q) e ≤
      restrictColorPattern p e ⊔ restrictColorPattern q e) :
    restrictColorPattern (p ⊔ q) e =
      restrictColorPattern p e ⊔ restrictColorPattern q e := by
  apply le_antisymm hbridge
  exact join_restrictions_le_restrict_join p q e

#print axioms join_restrictions_le_restrict_join
#print axioms restrict_join_eq_of_no_external_bridge

end LC004
