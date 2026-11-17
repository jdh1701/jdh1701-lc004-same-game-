import LC004.FivePatternCoordinates
import LC004.IncidenceFaceSum

namespace LC004
open scoped Classical

noncomputable def fiveEncodedPattern {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (a : Fin (Fintype.card (Quotient p)) → Fin 10) : ColorPattern n :=
  Setoid.comap (fivePatternCoordinates p hfive) (fiveAssignmentSetoid a)

theorem fiveEncodedPattern_refines {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (a : Fin (Fintype.card (Quotient p)) → Fin 10) : fiveEncodedPattern p hfive a ≤ p := by
  intro x y hxy
  apply (Setoid.ext_iff.mp (fivePatternCoordinates_base p hfive) x y).mpr
  exact fiveAssignmentSetoid_le_base a hxy

theorem fiveEncodedPattern_injective {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    Function.Injective (fiveEncodedPattern p hfive) := by
  intro a b h
  exact fiveAssignmentSetoid_injective
    (setoid_comap_equiv_injective (fivePatternCoordinates p hfive) h)

theorem fiveEncodedPattern_sizes {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (a : Fin (Fintype.card (Quotient p)) → Fin 10) :
    ∀ x, (patternClassPositions (fiveEncodedPattern p hfive a) x).card = 2 ∨
      (patternClassPositions (fiveEncodedPattern p hfive a) x).card = 3 := by
  have hs := five_encoded_small_classes (fivePatternCoordinates p hfive) a
  intro x
  simpa only [SetoidSmallClasses23,setoidClassFinset,patternClassPositions,fiveEncodedPattern] using hs x

/-- Original unlabeled certificate generators below p are exactly the uniquely
encoded tuples whose ORIGINAL position pattern is noncrossing. This is a full
bijection, with no assumed representation or omitted inverse direction. -/
noncomputable def fiveCertificateGeneratorEquiv {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    {a : Fin (Fintype.card (Quotient p)) → Fin 10 //
      PatternNoncrossing (fiveEncodedPattern p hfive a)} ≃
    {c : ColorPattern n // CertificateConstraint c ∧ c ≤ p} :=
  Equiv.ofBijective
    (fun a => ⟨fiveEncodedPattern p hfive a.val,
      ⟨fiveEncodedPattern_sizes p hfive a.val,a.property⟩,fiveEncodedPattern_refines p hfive a.val⟩)
    ⟨fun a b h => Subtype.ext (fiveEncodedPattern_injective p hfive (congrArg Subtype.val h)), by
      rintro ⟨c,⟨hsize,hnc⟩,hcp⟩
      have hs : SetoidSmallClasses23 c := by
        intro x
        simpa only [setoidClassFinset,patternClassPositions] using hsize x
      obtain ⟨a,ha,_⟩ := five_original_small_refinement_unique p hfive c hcp hs
      have hncA : PatternNoncrossing (fiveEncodedPattern p hfive a) := by
        change PatternNoncrossing (Setoid.comap (fivePatternCoordinates p hfive) (fiveAssignmentSetoid a))
        rw [← ha]
        exact hnc
      exact ⟨⟨a,hncA⟩,Subtype.ext ha.symm⟩⟩

theorem winning_below_five_iff_encoded_tuple {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (r : ColorPattern n) (hrp : r ≤ p) :
    WinningColorPattern r ↔ ∃ a,
      PatternNoncrossing (fiveEncodedPattern p hfive a) ∧ fiveEncodedPattern p hfive a ≤ r := by
  constructor
  · intro hwin
    obtain ⟨c,hc,hcr⟩ := (winning_iff_constraint_refinement r).mp hwin
    obtain ⟨a,ha⟩ := (fiveCertificateGeneratorEquiv p hfive).surjective ⟨c,hc,hcr.trans hrp⟩
    have he : fiveEncodedPattern p hfive a.val = c := congrArg Subtype.val ha
    exact ⟨a.val,a.property,he ▸ hcr⟩
  · rintro ⟨a,hnc,har⟩
    exact (winning_iff_constraint_refinement r).mpr
      ⟨fiveEncodedPattern p hfive a,⟨fiveEncodedPattern_sizes p hfive a,hnc⟩,har⟩

#print axioms fiveCertificateGeneratorEquiv
#print axioms winning_below_five_iff_encoded_tuple
end LC004
