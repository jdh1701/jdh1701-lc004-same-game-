import LC004.HeavyFaceRestriction
import LC004.RigidFaceArcCriterion

namespace LC004

theorem certificate_position_rigid_or_heavy {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p)) (i : Fin n) :
    RigidPosition p i ∨ HeavyPosition p i := by
  classical
  obtain ⟨b, hb, hi⟩ := cert.cover_position i
  have hsub := certificate_block_subset_class p cert hb hi
  have hle := Finset.card_le_card hsub
  have hn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  rw [List.toFinset_card_of_nodup hn] at hle
  have hs := cert.sizes b hb
  unfold RigidPosition HeavyPosition
  omega

theorem certificate_rigid_related {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {a b : Fin n} (ha : RigidPosition p a) (hab : p a b) :
    certificateBlockPattern cert a b := by
  classical
  obtain ⟨block, hb, ha'⟩ := cert.cover_position a
  refine ⟨block, hb, ha', ?_⟩
  apply List.mem_toFinset.mp
  rw [certificate_rigid_block_eq_class p cert hb ha' ha]
  simpa only [patternClassPositions, Finset.mem_filter,
    Finset.mem_univ, true_and] using hab

/-- A certificate partition is determined by its restrictions to heavy
faces: the rigid classes leave no choices. Equality here forgets the
irrelevant ordering of blocks and positions inside a certificate list. -/
theorem certificate_pattern_determined_by_heavy_faces {n : Nat} (p : ColorPattern n)
    (c d : Noncrossing23Certificate (patternColor p))
    (hfaces : ∀ a : Fin n,
      restrictColorPattern (certificateBlockPattern c) (heavyFaceEmbedding p a) =
      restrictColorPattern (certificateBlockPattern d) (heavyFaceEmbedding p a)) :
    certificateBlockPattern c = certificateBlockPattern d := by
  have forward (c d : Noncrossing23Certificate (patternColor p))
      (hfaces : ∀ a : Fin n,
        restrictColorPattern (certificateBlockPattern c) (heavyFaceEmbedding p a) =
        restrictColorPattern (certificateBlockPattern d) (heavyFaceEmbedding p a)) :
      certificateBlockPattern c ≤ certificateBlockPattern d := by
    intro a b hab
    rcases certificate_position_rigid_or_heavy p c a with ha | ha
    · exact certificate_rigid_related p d ha (certificateBlockPattern_refines p c hab)
    · obtain ⟨hb, hface⟩ := certificate_heavy_face p c ha hab
      have hcarrier := heavyFaceEmbedding_carrier p a
      obtain ⟨i, hi⟩ := (hcarrier a).mpr ⟨ha, (rigidFacePattern p).refl a⟩
      obtain ⟨j, hj⟩ := (hcarrier b).mpr ⟨hb, hface⟩
      have hlocal : restrictColorPattern (certificateBlockPattern c)
          (heavyFaceEmbedding p a) i j := by
        apply (restrictColorPattern_rel _ _ i j).mpr
        simpa only [hi, hj] using hab
      rw [hfaces a] at hlocal
      have hout := (restrictColorPattern_rel (certificateBlockPattern d)
        (heavyFaceEmbedding p a) i j).mp hlocal
      simpa only [hi, hj] using hout
  exact le_antisymm (forward c d hfaces) (forward d c (fun a => (hfaces a).symm))

#print axioms certificate_position_rigid_or_heavy
#print axioms certificate_pattern_determined_by_heavy_faces

end LC004
