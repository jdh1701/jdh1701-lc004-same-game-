import LC004.FaceRestriction

namespace LC004

/-- A step in the union of two equivalence relations. -/
def FaceJoinEdge {n : Nat} (p q : ColorPattern n) (a b : Fin n) : Prop :=
  p a b ∨ q a b

/-- A finite path made from steps in either equivalence relation. -/
def FaceJoinPath {n : Nat} (p q : ColorPattern n) (a b : Fin n) : Prop :=
  Relation.ReflTransGen (FaceJoinEdge p q) a b

/-- Every single p-edge gives a path. -/
theorem faceJoinPath_of_left {n : Nat} (p q : ColorPattern n)
    {a b : Fin n} (h : p a b) : FaceJoinPath p q a b := by
  exact Relation.ReflTransGen.single (Or.inl h)

/-- Every single q-edge gives a path. -/
theorem faceJoinPath_of_right {n : Nat} (p q : ColorPattern n)
    {a b : Fin n} (h : q a b) : FaceJoinPath p q a b := by
  exact Relation.ReflTransGen.single (Or.inr h)

/-- Every finite p/q path is an identification in the global join. -/
theorem faceJoinPath_le_join {n : Nat} (p q : ColorPattern n)
    {a b : Fin n} (h : FaceJoinPath p q a b) :
    (p ⊔ q) a b := by
  induction h with
  | refl =>
      exact (p ⊔ q).refl _
  | tail hab hbc ih =>
      apply (p ⊔ q).trans ih
      rcases hbc with hp | hq
      · exact le_sup_left hp
      · exact le_sup_right hq

#print axioms faceJoinPath_le_join

end LC004
