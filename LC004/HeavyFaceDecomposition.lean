import LC004.OrderedCertificateAssembly
import LC004.HeavyFaceReconstruction

namespace LC004

/-- Every color appearing in the word occurs at least twice. -/
def NoSingletonColors {n : Nat} (p : ColorPattern n) : Prop :=
  ∀ i, 2 ≤ (patternClassPositions p i).card

/-- Alternating chords of rigid color classes are forbidden. This includes
the possibility that the two chords have the same color. -/
def RigidSkeletonNoncrossing {n : Nat} (p : ColorPattern n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    RigidPosition p a → RigidPosition p b → p a c → p b d → False

abbrev HeavyFaceRegionIndex {n : Nat} (p : ColorPattern n) :=
  {q : Quotient p // RigidPosition p q.out} ⊕ Quotient (rigidFacePattern p)

/-- One region per rigid color class and one per geometric face. Heavy
faces with no positions are harmless empty regions. Quotient indices avoid
duplicating a region for each possible anchor. -/
noncomputable def heavyFaceRegion {n : Nat} (p : ColorPattern n) :
    HeavyFaceRegionIndex p → Finset (Fin n)
  | .inl q => patternClassPositions p q.val.out
  | .inr q => heavyFacePositions p q.out

theorem rigidPosition_of_related {n : Nat} (p : ColorPattern n)
    {a b : Fin n} (ha : RigidPosition p a) (hab : p a b) : RigidPosition p b := by
  unfold RigidPosition at *
  rwa [← patternClassPositions_eq_of_related p hab]

theorem quotient_eq_of_out_related {n : Nat} (p : ColorPattern n)
    (q r : Quotient p) (h : p q.out r.out) : q = r := by
  simpa only [Quotient.out_eq] using (Quotient.sound h)

theorem heavyFaceRegion_cover {n : Nat} (p : ColorPattern n)
    (hsize : NoSingletonColors p) (a : Fin n) :
    ∃ k, a ∈ heavyFaceRegion p k := by
  classical
  by_cases ha : RigidPosition p a
  · let q : Quotient p := Quotient.mk p a
    have hqa : p q.out a := Quotient.exact (Quotient.out_eq q)
    have hq : RigidPosition p q.out := rigidPosition_of_related p ha (p.symm hqa)
    refine ⟨Sum.inl ⟨q, hq⟩, ?_⟩
    simpa [heavyFaceRegion, patternClassPositions] using hqa
  · have hh : HeavyPosition p a := by
      have hs := hsize a
      unfold RigidPosition at ha
      unfold HeavyPosition
      omega
    let q : Quotient (rigidFacePattern p) := Quotient.mk _ a
    have hqa : rigidFacePattern p q.out a := Quotient.exact (Quotient.out_eq q)
    exact ⟨Sum.inr q, by simpa [heavyFaceRegion, heavyFacePositions] using And.intro hh hqa⟩

theorem heavyFaceRegion_disjoint {n : Nat} (p : ColorPattern n)
    (k l : HeavyFaceRegionIndex p) (a : Fin n)
    (hk : a ∈ heavyFaceRegion p k) (hl : a ∈ heavyFaceRegion p l) : k = l := by
  classical
  cases k with
  | inl q =>
    have hqa : p q.val.out a := by simpa [heavyFaceRegion, patternClassPositions] using hk
    have ha := rigidPosition_of_related p q.property hqa
    cases l with
    | inl r =>
      have hra : p r.val.out a := by simpa [heavyFaceRegion, patternClassPositions] using hl
      have heq := quotient_eq_of_out_related p q.val r.val (p.trans hqa (p.symm hra))
      exact congrArg Sum.inl (Subtype.ext heq)
    | inr r =>
      have hh : HeavyPosition p a := (show HeavyPosition p a ∧ _ by
        simpa [heavyFaceRegion, heavyFacePositions] using hl).1
      exact (heavy_ne_rigid p hh ha rfl).elim
  | inr q =>
    have hqa : HeavyPosition p a ∧ rigidFacePattern p q.out a := by
      simpa [heavyFaceRegion, heavyFacePositions] using hk
    cases l with
    | inl r =>
      have hra : p r.val.out a := by simpa [heavyFaceRegion, patternClassPositions] using hl
      exact (heavy_ne_rigid p hqa.1 (rigidPosition_of_related p r.property hra) rfl).elim
    | inr r =>
      have hra : HeavyPosition p a ∧ rigidFacePattern p r.out a := by
        simpa [heavyFaceRegion, heavyFacePositions] using hl
      exact congrArg Sum.inr (quotient_eq_of_out_related (rigidFacePattern p) q r
        ((rigidFacePattern p).trans hqa.2 ((rigidFacePattern p).symm hra.2)))

theorem heavyFaceRegion_noncrossing {n : Nat} (p : ColorPattern n)
    (hskel : RigidSkeletonNoncrossing p)
    (k l : HeavyFaceRegionIndex p) (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ heavyFaceRegion p k) (hc : c ∈ heavyFaceRegion p k)
    (hb : b ∈ heavyFaceRegion p l) (hd : d ∈ heavyFaceRegion p l) : k = l := by
  classical
  cases k with
  | inl q =>
    have hqa : p q.val.out a := by simpa [heavyFaceRegion, patternClassPositions] using ha
    have hqc : p q.val.out c := by simpa [heavyFaceRegion, patternClassPositions] using hc
    have hra := rigidPosition_of_related p q.property hqa
    have hac := p.trans (p.symm hqa) hqc
    cases l with
    | inl r =>
      have hrb : p r.val.out b := by simpa [heavyFaceRegion, patternClassPositions] using hb
      have hrd : p r.val.out d := by simpa [heavyFaceRegion, patternClassPositions] using hd
      exact (hskel a b c d hab hbc hcd hra (rigidPosition_of_related p r.property hrb)
        hac (p.trans (p.symm hrb) hrd)).elim
    | inr r =>
      have hrb : HeavyPosition p b ∧ rigidFacePattern p r.out b := by
        simpa [heavyFaceRegion, heavyFacePositions] using hb
      have hrd : HeavyPosition p d ∧ rigidFacePattern p r.out d := by
        simpa [heavyFaceRegion, heavyFacePositions] using hd
      have hbd := (rigidFacePattern p).trans ((rigidFacePattern p).symm hrb.2) hrd.2
      have h := (hbd a c hra hac).mp ⟨hab, hbc⟩
      omega
  | inr q =>
    have hqa : HeavyPosition p a ∧ rigidFacePattern p q.out a := by
      simpa [heavyFaceRegion, heavyFacePositions] using ha
    have hqc : HeavyPosition p c ∧ rigidFacePattern p q.out c := by
      simpa [heavyFaceRegion, heavyFacePositions] using hc
    have hac := (rigidFacePattern p).trans ((rigidFacePattern p).symm hqa.2) hqc.2
    cases l with
    | inl r =>
      have hrb : p r.val.out b := by simpa [heavyFaceRegion, patternClassPositions] using hb
      have hrd : p r.val.out d := by simpa [heavyFaceRegion, patternClassPositions] using hd
      have hr := rigidPosition_of_related p r.property hrb
      have hbd := p.trans (p.symm hrb) hrd
      have h := (hac b d hr hbd).mpr ⟨hbc, hcd⟩
      omega
    | inr r =>
      have hrb : HeavyPosition p b ∧ rigidFacePattern p r.out b := by
        simpa [heavyFaceRegion, heavyFacePositions] using hb
      have hrd : HeavyPosition p d ∧ rigidFacePattern p r.out d := by
        simpa [heavyFaceRegion, heavyFacePositions] using hd
      have hbd := (rigidFacePattern p).trans ((rigidFacePattern p).symm hrb.2) hrd.2
      have hafb := rigid_faces_no_alternation p hab hbc hcd hac hbd
      exact congrArg Sum.inr (quotient_eq_of_out_related (rigidFacePattern p) q r
        ((rigidFacePattern p).trans hqa.2
          ((rigidFacePattern p).trans hafb ((rigidFacePattern p).symm hrb.2))))

theorem winning_restrict_rigid_class {n : Nat} (p : ColorPattern n)
    (a : Fin n) (ha : RigidPosition p a) :
    WinningColorPattern (restrictColorPattern p
      ((patternClassPositions p a).orderEmbOfFin rfl)) := by
  classical
  let e := (patternClassPositions p a).orderEmbOfFin rfl
  have he (i) : p a (e i) := by
    have hi : e i ∈ patternClassPositions p a :=
      (patternClassPositions p a).orderEmbOfFin_mem rfl i
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  have sat : ∀ i b, p (e i) b → ∃ j, e j = b := by
    intro i b hib
    have hb : b ∈ patternClassPositions p a := by
      simpa [patternClassPositions] using p.trans (he i) hib
    change b ∈ Set.range e
    simpa [e, Finset.range_orderEmbOfFin] using hb
  apply (winning_iff_constraint_refinement _).mpr
  refine ⟨restrictColorPattern p e, ⟨?_, ?_⟩, le_rfl⟩
  · intro i
    rw [restrict_pattern_class_card p e sat i,
      ← patternClassPositions_eq_of_related p (he i)]
    exact ha
  · intro i j k l _ _ _ _ _
    exact (restrictColorPattern_rel p e i j).mpr (p.trans (p.symm (he i)) (he j))

/-- The reverse geometric Face Lemma: rigid classes and independently
winning complete heavy faces assemble into a genuine Same Game win. -/
theorem winning_of_heavy_faces {n : Nat} (p : ColorPattern n)
    (hsize : NoSingletonColors p) (hskel : RigidSkeletonNoncrossing p)
    (hfaces : ∀ a, WinningColorPattern
      (restrictColorPattern p (heavyFaceEmbedding p a))) : WinningColorPattern p := by
  classical
  apply winning_of_noncrossing_finset_cover p (heavyFaceRegion p)
    (heavyFaceRegion_cover p hsize) (heavyFaceRegion_disjoint p)
    (heavyFaceRegion_noncrossing p hskel)
  intro k
  cases k with
  | inl q => exact winning_restrict_rigid_class p q.val.out q.property
  | inr q => exact hfaces q.out

/-- Full structural Face Decomposition Theorem. It has no assumed global
certificate, path-locality condition, saturation condition, or gluing oracle. -/
theorem winning_iff_heavy_face_decomposition {n : Nat} (p : ColorPattern n) :
    WinningColorPattern p ↔ NoSingletonColors p ∧ RigidSkeletonNoncrossing p ∧
      ∀ a, WinningColorPattern (restrictColorPattern p (heavyFaceEmbedding p a)) := by
  constructor
  · intro hwin
    obtain ⟨cert⟩ := hwin
    refine ⟨?_, ?_, fun a => winning_restrict_heavy_face p ⟨cert⟩ a⟩
    · intro i
      rcases certificate_position_rigid_or_heavy p cert i with h | h
      · rcases h with h | h <;> omega
      · exact le_trans (by decide : 2 ≤ 4) h
    · intro a b c d hab hbc hcd ha hb hac hbd
      have cc := certificateBlockPattern_constraint cert
      have hsmall : ∀ i, (patternClassPositions (certificateBlockPattern cert) i).card ≤ 3 := by
        intro i
        rcases cc.1 i with h | h <;> omega
      exact small_noncrossing_no_alternation _ hsmall cc.2 a b c d hab hbc hcd
        ⟨certificate_rigid_related p cert ha hac, certificate_rigid_related p cert hb hbd⟩
  · rintro ⟨hsize, hskel, hfaces⟩
    exact winning_of_heavy_faces p hsize hskel hfaces

/-- The same criterion for the original maximal-run deletion game, using
the original colors in every increasing face subword. -/
theorem raw_win_iff_heavy_face_decomposition {n q : Nat} (color : Fin n → Fin q) :
    RawMaxErases (List.ofFn color) [] ↔
      NoSingletonColors (colorPatternOf color) ∧
      RigidSkeletonNoncrossing (colorPatternOf color) ∧
      ∀ a, RawMaxErases (List.ofFn (fun i =>
        color (heavyFaceEmbedding (colorPatternOf color) a i))) [] := by
  rw [← winning_color_pattern_iff_raw_win, winning_iff_heavy_face_decomposition]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro a
  rw [← winning_color_pattern_iff_raw_win]
  have heq : colorPatternOf (fun i =>
      color (heavyFaceEmbedding (colorPatternOf color) a i)) =
      restrictColorPattern (colorPatternOf color) (heavyFaceEmbedding (colorPatternOf color) a) := by
    apply Setoid.ext
    intro i j
    exact (restrictColorPattern_rel (colorPatternOf color)
      (heavyFaceEmbedding (colorPatternOf color) a) i j).symm
  rw [heq]

#print axioms winning_of_heavy_faces
#print axioms winning_iff_heavy_face_decomposition
#print axioms raw_win_iff_heavy_face_decomposition

end LC004
