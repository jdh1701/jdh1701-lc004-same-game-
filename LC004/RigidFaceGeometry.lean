import LC004.SmallPatternCorrespondence
import LC004.FacePathFactorization

namespace LC004

/-- Rigidity is local to this color class; other classes may be heavy. -/
theorem certificate_rigid_block_eq_class {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {b : List (Fin n)} (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b)
    (hsmall : (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3) :
    b.toFinset = patternClassPositions p i := by
  classical
  have hsub := certificate_block_subset_class p cert hb hi
  apply Finset.eq_of_subset_of_card_le hsub
  by_contra hnot
  have hbn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  have hbc := List.toFinset_card_of_nodup hbn
  have hblen := cert.sizes b hb
  have hclass := hsmall
  have hdiff : ((patternClassPositions p i) \ b.toFinset).card = 1 := by
    rw [Finset.card_sdiff hsub]
    rcases hclass with h | h <;> rcases hblen with hlen | hlen <;> omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 <
    ((patternClassPositions p i) \ b.toFinset).card by omega)
  have hjc := (Finset.mem_sdiff.mp hj).1
  have hjnot := (Finset.mem_sdiff.mp hj).2
  have hij : p i j := by
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hjc
  obtain ⟨c, hc, hjmem⟩ := cert.cover_position j
  have hne : b ≠ c := by
    intro heq
    exact hjnot (List.mem_toFinset.mpr (heq.symm ▸ hjmem))
  have hdis := disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hc hne
  have hcsub : c.toFinset ⊆ (patternClassPositions p i) \ b.toFinset := by
    intro x hx
    have hxc := List.mem_toFinset.mp hx
    have hjx : p j x := by
      have h := certificate_block_subset_class p cert hc hjmem hx
      simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using h
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using p.trans hij hjx
    · intro hxb
      exact (List.disjoint_left.mp hdis) (List.mem_toFinset.mp hxb) hxc
  have hcle := Finset.card_le_card hcsub
  have hcn := (List.nodup_flatten.mp cert.flatten_nodup).1 c hc
  have hclen := cert.sizes c hc
  rw [List.toFinset_card_of_nodup hcn, hdiff] at hcle
  rcases hclen with h | h <;> omega

def RigidPosition {n : Nat} (p : ColorPattern n) (i : Fin n) : Prop :=
  (patternClassPositions p i).card = 2 ∨ (patternClassPositions p i).card = 3

def HeavyPosition {n : Nat} (p : ColorPattern n) (i : Fin n) : Prop :=
  4 ≤ (patternClassPositions p i).card

theorem patternClassPositions_eq_of_related {n : Nat} (p : ColorPattern n)
    {i j : Fin n} (h : p i j) :
    patternClassPositions p i = patternClassPositions p j := by
  classical
  ext x
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hx => p.trans (p.symm h) hx, fun hx => p.trans h hx⟩

/-- A face is determined by its side of every chord of a rigid color class.
On heavy positions no point lies on a boundary chord endpoint. The outer
face is included automatically; an empty skeleton gives one face. -/
def rigidFacePattern {n : Nat} (p : ColorPattern n) : ColorPattern n where
  r a b := ∀ u v : Fin n, RigidPosition p u → p u v →
    (u < a ∧ a < v ↔ u < b ∧ b < v)
  iseqv := ⟨fun _ _ _ _ _ => Iff.rfl,
    fun h u v hu huv => (h u v hu huv).symm,
    fun h₁ h₂ u v hu huv => (h₁ u v hu huv).trans (h₂ u v hu huv)⟩

theorem heavy_ne_rigid {n : Nat} (p : ColorPattern n) {a u : Fin n}
    (ha : HeavyPosition p a) (hu : RigidPosition p u) : a ≠ u := by
  rintro rfl
  unfold HeavyPosition at ha
  rcases hu with hu | hu <;> omega

/-- The geometric confinement theorem for actual Same Game certificates.
It is derived from local rigidity and alternating-endpoint exclusion;
no face-locality or saturation assumption is supplied. -/
theorem certificate_heavy_face {n : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    {a b : Fin n} (ha : HeavyPosition p a)
    (hab : certificateBlockPattern cert a b) :
    HeavyPosition p b ∧ rigidFacePattern p a b := by
  have hpab := certificateBlockPattern_refines p cert hab
  have hclass := patternClassPositions_eq_of_related p hpab
  have hb : HeavyPosition p b := by
    unfold HeavyPosition at *
    rwa [← hclass]
  refine ⟨hb, ?_⟩
  intro u v hu huv
  have hv : RigidPosition p v := by
    unfold RigidPosition at *
    rwa [← patternClassPositions_eq_of_related p huv]
  have hau := heavy_ne_rigid p ha hu
  have hav := heavy_ne_rigid p ha hv
  have hbu := heavy_ne_rigid p hb hu
  have hbv := heavy_ne_rigid p hb hv
  obtain ⟨c, hc, hac, hbc⟩ := hab
  obtain ⟨r, hr, hur⟩ := cert.cover_position u
  have hrclass := certificate_rigid_block_eq_class p cert hr hur hu
  have hvr : v ∈ r := by
    apply List.mem_toFinset.mp
    rw [hrclass]
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using huv
  have h₁ := cert.no_alternation hr hc hur hvr hac hbc
  have h₂ := cert.no_alternation hr hc hur hvr hbc hac
  unfold PairCross at h₁ h₂
  constructor <;> intro h <;> constructor <;> omega

/-- Distinct geometric faces cannot contain alternating endpoint pairs.
This supplies the geometric part of gluing certificates from faces. -/
theorem rigid_faces_no_alternation {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : rigidFacePattern p a c) (hbd : rigidFacePattern p b d) :
    rigidFacePattern p a b := by
  intro u v hu huv
  have h₁ := hac u v hu huv
  have h₂ := hbd u v hu huv
  constructor <;> intro h <;> constructor <;> omega

/-- A genuine full face carrier, rather than an arbitrary selection of
positions or a partial face. -/
def IsHeavyFaceCarrier {n m : Nat} (p : ColorPattern n)
    (anchor : Fin n) (e : Fin m → Fin n) : Prop :=
  ∀ x, (∃ i, e i = x) ↔ HeavyPosition p x ∧ rigidFacePattern p anchor x

theorem certificate_face_saturated {n m : Nat} (p : ColorPattern n)
    (cert : Noncrossing23Certificate (patternColor p))
    (anchor : Fin n) (e : Fin m → Fin n)
    (hface : IsHeavyFaceCarrier p anchor e)
    {i : Fin m} {b : Fin n} (h : certificateBlockPattern cert (e i) b) :
    ∃ j, e j = b := by
  have hi := (hface (e i)).mp ⟨i, rfl⟩
  obtain ⟨hb, hab⟩ := certificate_heavy_face p cert hi.1 h
  exact (hface b).mpr ⟨hb, (rigidFacePattern p).trans hi.2 hab⟩

theorem facePathLocality_of_edge_saturation {n m : Nat}
    (p q : ColorPattern n) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (hsat : ∀ i b, FaceJoinEdge p q (e i) b → ∃ j, e j = b) :
    FacePathLocality p q e := by
  intro i j h
  have lift : ∀ {a b : Fin n}, FaceJoinPath p q a b →
      ∀ i : Fin m, e i = a → ∃ k, e k = b ∧ FaceInternalPath p q e i k := by
    intro a b hab
    induction hab with
    | refl =>
        intro i hi
        exact ⟨i, hi, Relation.ReflTransGen.refl⟩
    | @tail b c hab hbc ih =>
        intro i hi
        obtain ⟨k, hk, hik⟩ := ih i hi
        obtain ⟨l, hl⟩ := hsat k c (hk.symm ▸ hbc)
        refine ⟨l, hl, Relation.ReflTransGen.tail hik ?_⟩
        change p (e k) (e l) ∨ q (e k) (e l)
        rw [hk, hl]
        exact hbc
  obtain ⟨k, hk, hik⟩ := lift h i rfl
  exact he hk ▸ hik

/-- The former locality hypothesis now follows from actual certificate
geometry, for any two certificates of the same color pattern. -/
theorem heavy_certificate_face_path_locality {n m : Nat} (p : ColorPattern n)
    (c d : Noncrossing23Certificate (patternColor p))
    (anchor : Fin n) (e : Fin m → Fin n) (he : Function.Injective e)
    (hface : IsHeavyFaceCarrier p anchor e) :
    FacePathLocality (certificateBlockPattern c) (certificateBlockPattern d) e := by
  apply facePathLocality_of_edge_saturation _ _ e he
  intro i b h
  rcases h with hc | hd
  · exact certificate_face_saturated p c anchor e hface hc
  · exact certificate_face_saturated p d anchor e hface hd

theorem heavy_certificate_restrict_join {n m : Nat} (p : ColorPattern n)
    (c d : Noncrossing23Certificate (patternColor p))
    (anchor : Fin n) (e : Fin m → Fin n) (he : Function.Injective e)
    (hface : IsHeavyFaceCarrier p anchor e) :
    restrictColorPattern (certificateBlockPattern c ⊔ certificateBlockPattern d) e =
      restrictColorPattern (certificateBlockPattern c) e ⊔
        restrictColorPattern (certificateBlockPattern d) e :=
  restrict_join_eq_of_face_path_locality _ _ e
    (heavy_certificate_face_path_locality p c d anchor e he hface)

/-- Canonical increasing list of every heavy position in an actual face. -/
noncomputable def heavyFacePositions {n : Nat} (p : ColorPattern n) (a : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => HeavyPosition p x ∧ rigidFacePattern p a x)

noncomputable def heavyFaceEmbedding {n : Nat} (p : ColorPattern n) (a : Fin n) :
    Fin (heavyFacePositions p a).card ↪o Fin n := by
  classical
  exact (heavyFacePositions p a).orderEmbOfFin rfl

theorem heavyFaceEmbedding_carrier {n : Nat} (p : ColorPattern n) (a : Fin n) :
    IsHeavyFaceCarrier p a (heavyFaceEmbedding p a) := by
  classical
  intro x
  change x ∈ Set.range (heavyFaceEmbedding p a) ↔ _
  rw [heavyFaceEmbedding, Finset.range_orderEmbOfFin]
  simp [heavyFacePositions]

/-- No user-supplied locality or carrier hypothesis remains: the map is
the canonical increasing enumeration of the complete geometric face. -/
theorem canonical_heavy_face_restrict_join {n : Nat} (p : ColorPattern n)
    (c d : Noncrossing23Certificate (patternColor p)) (a : Fin n) :
    restrictColorPattern (certificateBlockPattern c ⊔ certificateBlockPattern d)
        (heavyFaceEmbedding p a) =
      restrictColorPattern (certificateBlockPattern c) (heavyFaceEmbedding p a) ⊔
        restrictColorPattern (certificateBlockPattern d) (heavyFaceEmbedding p a) :=
  heavy_certificate_restrict_join p c d a (heavyFaceEmbedding p a)
    (heavyFaceEmbedding p a).injective (heavyFaceEmbedding_carrier p a)

#print axioms certificate_rigid_block_eq_class
#print axioms certificate_heavy_face
#print axioms rigid_faces_no_alternation
#print axioms heavy_certificate_face_path_locality
#print axioms heavy_certificate_restrict_join
#print axioms canonical_heavy_face_restrict_join

end LC004

