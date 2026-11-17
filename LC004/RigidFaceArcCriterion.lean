import LC004.RigidFaceGeometry

namespace LC004

/-- For heavy endpoints in increasing order, the chord-signature faces
agree exactly with the paper's condition that no rigid class meets both
open cyclic arcs between the endpoints. No drawing is assumed. -/
theorem rigid_face_iff_no_rigid_arc_separator {n : Nat} (p : ColorPattern n)
    {a b : Fin n} (hab : a < b)
    (ha : HeavyPosition p a) (hb : HeavyPosition p b) :
    rigidFacePattern p a b ↔
      ¬ ∃ u v : Fin n, RigidPosition p u ∧ p u v ∧
        a < u ∧ u < b ∧ (v < a ∨ b < v) := by
  constructor
  · intro hface hsep
    obtain ⟨u, v, hu, huv, hau, hub, hvout⟩ := hsep
    rcases hvout with hva | hbv
    · have hv : RigidPosition p v := by
        unfold RigidPosition at *
        rwa [← patternClassPositions_eq_of_related p huv]
      have h := (hface v u hv (p.symm huv)).mp ⟨hva, hau⟩
      omega
    · have h := (hface u v hu huv).mpr ⟨hub, hbv⟩
      omega
  · intro hsep u v hu huv
    have hv : RigidPosition p v := by
      unfold RigidPosition at *
      rwa [← patternClassPositions_eq_of_related p huv]
    have hau := heavy_ne_rigid p ha hu
    have hav := heavy_ne_rigid p ha hv
    have hbu := heavy_ne_rigid p hb hu
    have hbv := heavy_ne_rigid p hb hv
    constructor
    · intro h
      by_contra hn
      have hvb : v < b := by omega
      exact hsep ⟨v, u, hv, p.symm huv, h.2, hvb, Or.inl h.1⟩
    · intro h
      by_contra hn
      have hau' : a < u := by omega
      exact hsep ⟨u, v, hu, huv, hau', h.1, Or.inr h.2⟩

#print axioms rigid_face_iff_no_rigid_arc_separator

end LC004
