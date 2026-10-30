import LC004.FaceJoinPaths

namespace LC004

/-- Local paths use only vertices selected by the face map. -/
def FaceInternalPath {n m : Nat} (p q : ColorPattern n)
    (e : Fin m → Fin n) (i j : Fin m) : Prop :=
  Relation.ReflTransGen
    (fun a b : Fin m => p (e a) (e b) ∨ q (e a) (e b)) i j

/-- Internal paths imply equivalence in the join of restricted patterns. -/
theorem faceInternalPath_sound {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n)
    {i j : Fin m} (h : FaceInternalPath p q e i j) :
    (restrictColorPattern p e ⊔ restrictColorPattern q e) i j := by
  induction h with
  | refl =>
      exact (restrictColorPattern p e ⊔ restrictColorPattern q e).refl _
  | tail hab hbc ih =>
      apply (restrictColorPattern p e ⊔ restrictColorPattern q e).trans ih
      rcases hbc with hp | hq
      · exact (show restrictColorPattern p e ≤ restrictColorPattern p e ⊔ restrictColorPattern q e from le_sup_left) ((restrictColorPattern_rel p e _ _).mpr hp)
      · exact (show restrictColorPattern q e ≤ restrictColorPattern p e ⊔ restrictColorPattern q e from le_sup_right) ((restrictColorPattern_rel q e _ _).mpr hq)

/-- The meaningful face-locality condition replaces any global path
between selected endpoints by an internal path. -/
def FacePathLocality {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n) : Prop :=
  ∀ i j : Fin m, FaceJoinPath p q (e i) (e j) →
    FaceInternalPath p q e i j

#print axioms faceInternalPath_sound

end LC004
