import LC004.FaceInternalPaths

namespace LC004

/-- Every global join identification has a finite p/q path witness.
The join is the least equivalence relation containing both relations. -/
theorem faceJoinPath_complete {n : Nat} (p q : ColorPattern n)
    {a b : Fin n} (h : (p ⊔ q) a b) :
    FaceJoinPath p q a b := by
  let R : Setoid (Fin n) := {
    r := FaceJoinPath p q
    iseqv := ⟨
      (fun a => Relation.ReflTransGen.refl),
      (fun a b hab => by
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | tail hab hbc ih =>
          have hs : FaceJoinEdge p q _ _ := by
            rcases hbc with hp | hq
            · exact Or.inl (p.symm hp)
            · exact Or.inr (q.symm hq)
          exact Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single hs) ih),
      (fun a b c hab hbc => Relation.ReflTransGen.trans hab hbc)⟩
  }
  have hp : p ≤ R := by
    intro i j hij
    exact Relation.ReflTransGen.single (Or.inl hij)
  have hq : q ≤ R := by
    intro i j hij
    exact Relation.ReflTransGen.single (Or.inr hij)
  exact (sup_le hp hq) h

/-- Face-locality is sufficient for restriction to preserve binary joins. -/
theorem restrict_join_eq_of_face_path_locality {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n)
    (hlocal : FacePathLocality p q e) :
    restrictColorPattern (p ⊔ q) e =
      restrictColorPattern p e ⊔ restrictColorPattern q e := by
  apply le_antisymm
  · intro i j hij
    have hglobal : (p ⊔ q) (e i) (e j) :=
      (restrictColorPattern_rel (p ⊔ q) e i j).mp hij
    exact faceInternalPath_sound p q e
      (hlocal i j (faceJoinPath_complete p q hglobal))
  · apply sup_le
    · exact restrictColorPattern_mono le_sup_left e
    · exact restrictColorPattern_mono le_sup_right e

#print axioms faceJoinPath_complete
#print axioms restrict_join_eq_of_face_path_locality

end LC004
