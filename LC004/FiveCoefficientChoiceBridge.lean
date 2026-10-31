import LC004.FiveClassSeparators

namespace LC004
open scoped Classical

noncomputable def fiveEncodedNCTuples {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    Finset (Fin (Fintype.card (Quotient p)) → Fin 10) :=
  Finset.univ.filter (fun a => PatternNoncrossing (fiveEncodedPattern p hfive a))

def fivePairVertex (k : Nat) : (Sigma (fun _ : Fin k => Fin 10)) ↪ (Fin k × FiveCut) where
  toFun v := (v.1,Sum.inr v.2)
  inj' := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hij : i = j := congrArg Prod.fst he
    subst j
    have hst : s = t := Sum.inr.inj (congrArg Prod.snd he)
    subst t
    rfl

theorem fiveEncodedPattern_facet {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (a : Fin (Fintype.card (Quotient p)) → Fin 10) :
    indexedCoarseningFacet Finset.univ (fiveOriginalSeparator p hfive) (fiveEncodedPattern p hfive a) =
      (choiceFacet a).image (fivePairVertex _) := by
  classical
  ext v
  rcases v with ⟨i,t⟩
  have hle : fiveEncodedPattern p hfive a ≤ fiveOriginalSeparator p hfive (i,t) ↔
      t = Sum.inr (a i) :=
    (setoid_comap_equiv_le_iff (fivePatternCoordinates p hfive) _ _).trans
      (fiveAssignment_le_separator_iff a i t)
  simp only [indexedCoarseningFacet,Finset.mem_filter,Finset.mem_univ,true_and,hle]
  constructor
  · intro ht
    exact Finset.mem_image.mpr ⟨Sigma.mk i (a i),(mem_choiceFacet a i (a i)).mpr rfl,
      by simpa only [fivePairVertex,Function.Embedding.coeFn_mk] using congrArg (Prod.mk i) ht.symm⟩
  · intro hv
    obtain ⟨⟨j,s⟩,hjs,he⟩ := Finset.mem_image.mp hv
    have hji : j = i := congrArg Prod.fst he
    subst j
    have hai : a i = s := (mem_choiceFacet a i s).mp hjs
    have hst : Sum.inr s = t := congrArg Prod.snd he
    exact hst.symm.trans (congrArg Sum.inr hai.symm)

theorem five_certificate_generators_image {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    Finset.univ.filter (fun c : ColorPattern n => CertificateConstraint c ∧ c ≤ p) =
      (fiveEncodedNCTuples p hfive).image (fiveEncodedPattern p hfive) := by
  classical
  ext c
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro hc
    obtain ⟨a,ha⟩ := (fiveCertificateGeneratorEquiv p hfive).surjective ⟨c,hc⟩
    exact ⟨a.val,by simpa [fiveEncodedNCTuples] using a.property,congrArg Subtype.val ha⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨fiveEncodedPattern_sizes p hfive a,by simpa [fiveEncodedNCTuples] using ha⟩,
      fiveEncodedPattern_refines p hfive a⟩

theorem five_indexed_facets_image {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    indexedCertificateCoarseningFacets p Finset.univ (fiveOriginalSeparator p hfive) =
      (choiceFacets (fiveEncodedNCTuples p hfive)).image (fun f => f.image (fivePairVertex _)) := by
  classical
  unfold indexedCertificateCoarseningFacets choiceFacets
  rw [five_certificate_generators_image]
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro a _
  exact fiveEncodedPattern_facet p hfive a

/-- The original game's collected join coefficient is exactly the alternating
choice-complex sum for its canonical split tuples. This closes the coefficient
identity itself, including all boundary cases, without assuming it as a hypothesis. -/
theorem winningJoinCoefficient_five_eq_choice_sum {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    winningJoinCoefficient n p =
      faceAlternatingSum (facetFaces (choiceFacets (fiveEncodedNCTuples p hfive))) := by
  classical
  have hc := winningJoinCoefficient_eq_indexed_face_sum p Finset.univ
    (fiveOriginalSeparator p hfive) (fun v _ => fiveOriginalSeparators_strict p hfive v)
    (fun q hq hne => by
      obtain ⟨v,hv⟩ := fiveOriginalSeparators_cover p hfive q hq hne
      exact ⟨v,Finset.mem_univ v,hv⟩)
  rw [five_indexed_facets_image] at hc
  exact hc.trans (facetAlternatingSum_image_embedding (choiceFacets (fiveEncodedNCTuples p hfive))
    (fivePairVertex _) (fivePairVertex _).injective)

#print axioms winningJoinCoefficient_five_eq_choice_sum
end LC004
