import LC004.HeavyFaceDecomposition

namespace LC004
open scoped Classical

/-- Unordered certificate partitions of a fixed color pattern. Neither
block order nor the order of entries inside a block is counted. -/
abbrev CertificatePartition {n : Nat} (p : ColorPattern n) :=
  {c : ColorPattern n // CertificateConstraint c ∧ c ≤ p}

noncomputable def CertificatePartition.toCertificate {n : Nat} {p : ColorPattern n}
    (c : CertificatePartition p) : Noncrossing23Certificate (patternColor p) :=
  (smallPatternCertificate c.val c.property.1.1 c.property.1.2).recolor
    (patternColor p) (fun i j h => (patternColor_eq_iff p i j).mpr
      (c.property.2 ((patternColor_eq_iff c.val i j).mp h)))

theorem CertificatePartition.toCertificate_pattern {n : Nat} {p : ColorPattern n}
    (c : CertificatePartition p) : certificateBlockPattern c.toCertificate = c.val := by
  change certificateBlockPattern
    (smallPatternCertificate c.val c.property.1.1 c.property.1.2) = c.val
  apply le_antisymm
  · intro i j h
    exact certificateBlockPattern_refines c.val _ h
  · intro i j h
    exact certificate_rigid_related c.val _ (c.property.1.1 i) h

/-- Restriction acts on actual partitions, retaining the exact pair/triple
classes, not merely the existence of some winning face certificate. -/
noncomputable def heavyFacePartitionRestriction {n : Nat} (p : ColorPattern n)
    (c : CertificatePartition p) (q : Quotient (rigidFacePattern p)) :
    CertificatePartition (restrictColorPattern p (heavyFaceEmbedding p q.out)) := by
  refine ⟨restrictColorPattern c.val (heavyFaceEmbedding p q.out), ?_,
    restrictColorPattern_mono c.property.2 _⟩
  apply certificateConstraint_restrict c.val c.property.1
  intro i b h
  rw [← c.toCertificate_pattern] at h
  exact certificate_face_saturated p c.toCertificate q.out (heavyFaceEmbedding p q.out)
    (heavyFaceEmbedding_carrier p q.out) h

abbrev HeavyFacePartitionFamily {n : Nat} (p : ColorPattern n) :=
  ∀ q : Quotient (rigidFacePattern p),
    CertificatePartition (restrictColorPattern p (heavyFaceEmbedding p q.out))

theorem heavyFacePartitionRestriction_injective {n : Nat} (p : ColorPattern n) :
    Function.Injective (heavyFacePartitionRestriction p) := by
  have forward (c d : CertificatePartition p)
      (h : heavyFacePartitionRestriction p c = heavyFacePartitionRestriction p d) :
      c.val ≤ d.val := by
    intro a b hab
    have hcert : certificateBlockPattern c.toCertificate a b := by
      rwa [c.toCertificate_pattern]
    rcases certificate_position_rigid_or_heavy p c.toCertificate a with ha | ha
    · have hd := certificate_rigid_related p d.toCertificate ha (c.property.2 hab)
      rwa [d.toCertificate_pattern] at hd
    · obtain ⟨hb, habf⟩ := certificate_heavy_face p c.toCertificate ha hcert
      let q : Quotient (rigidFacePattern p) := Quotient.mk _ a
      have hqa : rigidFacePattern p q.out a := Quotient.exact (Quotient.out_eq q)
      have carrier := heavyFaceEmbedding_carrier p q.out
      obtain ⟨i, hi⟩ := (carrier a).mpr ⟨ha, hqa⟩
      obtain ⟨j, hj⟩ := (carrier b).mpr ⟨hb, (rigidFacePattern p).trans hqa habf⟩
      have hlocal : restrictColorPattern c.val (heavyFaceEmbedding p q.out) i j := by
        apply (restrictColorPattern_rel _ _ i j).mpr
        simpa only [hi, hj] using hab
      have heq := congrArg Subtype.val (congrFun h q)
      change restrictColorPattern c.val (heavyFaceEmbedding p q.out) =
        restrictColorPattern d.val (heavyFaceEmbedding p q.out) at heq
      rw [heq] at hlocal
      have hout := (restrictColorPattern_rel d.val (heavyFaceEmbedding p q.out) i j).mp hlocal
      simpa only [hi, hj] using hout
  intro c d h
  exact Subtype.ext (le_antisymm (forward c d h) (forward d c h.symm))

/-- The assembly construction preserves every supplied regional partition
exactly. This is stronger than preservation of winning status. -/
theorem exists_partition_of_noncrossing_regions {n : Nat} {ι : Type*}
    (p : ColorPattern n) (S : ι → Finset (Fin n))
    (cover : ∀ a, ∃ k, a ∈ S k)
    (disjoint : ∀ k l a, a ∈ S k → a ∈ S l → k = l)
    (noncrossing : ∀ k l a b c d, a < b → b < c → c < d →
      a ∈ S k → c ∈ S k → b ∈ S l → d ∈ S l → k = l)
    (parts : ∀ k, CertificatePartition
      (restrictColorPattern p ((S k).orderEmbOfFin rfl))) :
    ∃ c : CertificatePartition p, ∀ k,
      restrictColorPattern c.val ((S k).orderEmbOfFin rfl) = (parts k).val := by
  classical
  let e := fun k => (S k).orderEmbOfFin rfl
  have coverE : ∀ a, ∃ k i, e k i = a := by
    intro a
    obtain ⟨k, hk⟩ := cover a
    refine ⟨k, ?_⟩
    change a ∈ Set.range (e k)
    simpa [e, Finset.range_orderEmbOfFin] using hk
  have disjointE : ∀ k l i j, e k i = e l j → k = l := by
    intro k l i j h
    apply disjoint k l (e k i) ((S k).orderEmbOfFin_mem rfl i)
    rw [h]
    exact (S l).orderEmbOfFin_mem rfl j
  have ncE : ∀ k l i j s t, e k i < e l s → e l s < e k j → e k j < e l t → k = l := by
    intro k l i j s t hab hbc hcd
    exact noncrossing k l _ _ _ _ hab hbc hcd
      ((S k).orderEmbOfFin_mem rfl i) ((S k).orderEmbOfFin_mem rfl j)
      ((S l).orderEmbOfFin_mem rfl s) ((S l).orderEmbOfFin_mem rfl t)
  let g := assembledPattern e (fun k => (parts k).val) coverE disjointE
  have hg : CertificateConstraint g := assembledPattern_constraint e _ coverE disjointE ncE
    (fun k => (parts k).property.1)
  have hgp : g ≤ p := by
    rintro a b ⟨k, i, j, rfl, rfl, hij⟩
    exact (restrictColorPattern_rel p (e k) i j).mp ((parts k).property.2 hij)
  refine ⟨⟨g, hg, hgp⟩, ?_⟩
  intro k
  apply Setoid.ext
  intro i j
  exact (restrictColorPattern_rel g (e k) i j).trans
    (assembledPattern_local e _ coverE disjointE k i j)

theorem heavyFacePartitionRestriction_surjective {n : Nat} (p : ColorPattern n)
    (hsize : NoSingletonColors p) (hskel : RigidSkeletonNoncrossing p) :
    Function.Surjective (heavyFacePartitionRestriction p) := by
  classical
  intro f
  have rigidWin (q : {q : Quotient p // RigidPosition p q.out}) :=
    (winning_iff_constraint_refinement _).mp
      (winning_restrict_rigid_class p q.val.out q.property)
  choose cr hcr href using rigidWin
  let parts : ∀ k : HeavyFaceRegionIndex p, CertificatePartition
      (restrictColorPattern p ((heavyFaceRegion p k).orderEmbOfFin rfl))
    | .inl q => ⟨cr q, hcr q, href q⟩
    | .inr q => f q
  obtain ⟨c, hc⟩ := exists_partition_of_noncrossing_regions p (heavyFaceRegion p)
    (heavyFaceRegion_cover p hsize) (heavyFaceRegion_disjoint p)
    (heavyFaceRegion_noncrossing p hskel) parts
  refine ⟨c, ?_⟩
  funext q
  apply Subtype.ext
  exact hc (.inr q)

/-- Exact, duplication-free certificate partition factorization over the
distinct geometric faces. Rigid blocks have no choices. -/
noncomputable def heavyFaceCertificateEquiv {n : Nat} (p : ColorPattern n)
    (hsize : NoSingletonColors p) (hskel : RigidSkeletonNoncrossing p) :
    CertificatePartition p ≃ HeavyFacePartitionFamily p :=
  Equiv.ofBijective (heavyFacePartitionRestriction p)
    ⟨heavyFacePartitionRestriction_injective p,
      heavyFacePartitionRestriction_surjective p hsize hskel⟩

/-- This counts certificate partitions for a fixed word. It does not count
winning color patterns or erasure histories. -/
theorem certificate_partition_count_product {n : Nat} (p : ColorPattern n)
    (hsize : NoSingletonColors p) (hskel : RigidSkeletonNoncrossing p) :
    Nat.card (CertificatePartition p) =
      ∏ q : Quotient (rigidFacePattern p),
        Nat.card (CertificatePartition (restrictColorPattern p (heavyFaceEmbedding p q.out))) := by
  classical
  rw [Nat.card_congr (heavyFaceCertificateEquiv p hsize hskel)]
  exact Nat.card_pi

#print axioms heavyFaceCertificateEquiv
#print axioms certificate_partition_count_product

end LC004
