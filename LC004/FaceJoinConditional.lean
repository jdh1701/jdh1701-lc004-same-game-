import LC004.FaceRestriction

namespace LC004

/-- A sufficient condition for join/restriction compatibility: the join
of the restricted relations already agrees with the restricted join.
The geometric Face Lemma must eventually supply this condition from
independence of certificates; it is not assumed universally. -/
theorem restrictColorPattern_join_of_rel_iff {n m : Nat}
    (p q : ColorPattern n) (embed : Fin m → Fin n)
    (h : ∀ i j : Fin m,
      (restrictColorPattern (p ⊔ q) embed) i j ↔
      (restrictColorPattern p embed ⊔ restrictColorPattern q embed) i j) :
    restrictColorPattern (p ⊔ q) embed =
      restrictColorPattern p embed ⊔ restrictColorPattern q embed := by
  apply Setoid.ext
  intro i j
  exact h i j

/-- Restricting an ambient coarsening preserves each constituent constraint. -/
theorem restrictColorPattern_join_upper {n m : Nat}
    (p q : ColorPattern n) (embed : Fin m → Fin n) :
    restrictColorPattern p embed ≤
      restrictColorPattern (p ⊔ q) embed := by
  exact restrictColorPattern_mono le_sup_left embed

#print axioms restrictColorPattern_join_of_rel_iff
#print axioms restrictColorPattern_join_upper

end LC004
