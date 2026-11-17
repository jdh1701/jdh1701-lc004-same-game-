import LC004.RigidFaceGeometry
import LC004.WinningConstraintGenerators

namespace LC004

/-- A saturated ordered restriction keeps every certificate class intact. -/
theorem restrict_pattern_class_card {n m : Nat} (c : ColorPattern n)
    (e : Fin m ↪o Fin n)
    (hsat : ∀ i b, c (e i) b → ∃ j, e j = b) (i : Fin m) :
    (patternClassPositions (restrictColorPattern c e) i).card =
      (patternClassPositions c (e i)).card := by
  classical
  have himage : (patternClassPositions (restrictColorPattern c e) i).image e =
      patternClassPositions c (e i) := by
    ext b
    simp only [Finset.mem_image, patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (restrictColorPattern_rel c e i j).mp hj
    · intro hb
      obtain ⟨j, rfl⟩ := hsat i b hb
      exact ⟨j, (restrictColorPattern_rel c e i j).mpr hb, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ e.injective]

theorem certificateConstraint_restrict {n m : Nat} (c : ColorPattern n)
    (hc : CertificateConstraint c) (e : Fin m ↪o Fin n)
    (hsat : ∀ i b, c (e i) b → ∃ j, e j = b) :
    CertificateConstraint (restrictColorPattern c e) := by
  constructor
  · intro i
    rw [restrict_pattern_class_card c e hsat]
    exact hc.1 (e i)
  · intro a b c' d hab hbc hcd hac hbd
    apply (restrictColorPattern_rel c e a b).mpr
    exact hc.2 (e a) (e b) (e c') (e d)
      (e.strictMono hab) (e.strictMono hbc) (e.strictMono hcd)
      ((restrictColorPattern_rel c e a c').mp hac)
      ((restrictColorPattern_rel c e b d).mp hbd)

/-- A global winning pattern gives a genuine winning subword in each
canonical geometric heavy face. This is the forward Face Lemma. -/
theorem winning_restrict_heavy_face {n : Nat} (p : ColorPattern n)
    (hwin : WinningColorPattern p) (a : Fin n) :
    WinningColorPattern (restrictColorPattern p (heavyFaceEmbedding p a)) := by
  obtain ⟨cert⟩ := hwin
  apply (winning_iff_constraint_refinement _).mpr
  refine ⟨restrictColorPattern (certificateBlockPattern cert) (heavyFaceEmbedding p a),
    ?_, ?_⟩
  · apply certificateConstraint_restrict _ (certificateBlockPattern_constraint cert)
    intro i b h
    exact certificate_face_saturated p cert a (heavyFaceEmbedding p a)
      (heavyFaceEmbedding_carrier p a) h
  · apply restrictColorPattern_mono
    intro i j h
    exact certificateBlockPattern_refines p cert h

/-- The restricted pattern has the same winning meaning as deleting all
maximal runs in the face word, with positions read in increasing order. -/
theorem raw_win_heavy_face_word {n : Nat} (p : ColorPattern n)
    (hwin : WinningColorPattern p) (a : Fin n) :
    RawMaxErases (List.ofFn (fun i => patternColor p (heavyFaceEmbedding p a i))) [] := by
  have heq : colorPatternOf (fun i => patternColor p (heavyFaceEmbedding p a i)) =
      restrictColorPattern p (heavyFaceEmbedding p a) := by
    apply Setoid.ext
    intro i j
    exact (patternColor_eq_iff p _ _).trans
      (restrictColorPattern_rel p (heavyFaceEmbedding p a) i j).symm
  apply (winning_color_pattern_iff_raw_win _).mp
  rw [heq]
  exact winning_restrict_heavy_face p hwin a

#print axioms certificateConstraint_restrict
#print axioms winning_restrict_heavy_face
#print axioms raw_win_heavy_face_word

end LC004
