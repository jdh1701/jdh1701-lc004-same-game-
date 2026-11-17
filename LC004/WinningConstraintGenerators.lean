import LC004.CertificateJoinIteration
import LC004.SmallPatternCorrespondence

namespace LC004
open scoped Classical

/-- Unlabeled pair/triple certificate partitions. -/
def CertificateConstraint {n : Nat} (p : ColorPattern n) : Prop :=
  (∀ i, (patternClassPositions p i).card = 2 ∨
    (patternClassPositions p i).card = 3) ∧ PatternNoncrossing p

theorem certificateBlockPattern_constraint {n q : Nat} {color : Fin n → Fin q}
    (cert : Noncrossing23Certificate color) :
    CertificateConstraint (certificateBlockPattern cert) := by
  classical
  constructor
  · intro i
    obtain ⟨b, hb, hi⟩ := cert.cover_position i
    rw [certificateBlockPattern_class cert hb hi,
      List.toFinset_card_of_nodup ((List.nodup_flatten.mp cert.flatten_nodup).1 b hb)]
    exact cert.sizes b hb
  · apply no_alternation_noncrossing
    rintro a b c d hab hbc hcd ⟨⟨ab, ha, hai, hac⟩, ⟨bb, hb, hbb, hbd⟩⟩
    exact cert.no_alternation ha hb hai hac hbb hbd (Or.inl ⟨hab, hbc, hcd⟩)

/-- Exact generator characterization, with no count or profile assumptions. -/
theorem winning_iff_constraint_refinement {n : Nat} (r : ColorPattern n) :
    WinningColorPattern r ↔ ∃ c : ColorPattern n, CertificateConstraint c ∧ c ≤ r := by
  constructor
  · rintro ⟨cert⟩
    exact ⟨certificateBlockPattern cert, certificateBlockPattern_constraint cert,
      fun _ _ h => certificateBlockPattern_refines r cert h⟩
  · rintro ⟨c, hc, hcr⟩
    exact winning_pattern_upward_closed hcr ⟨smallPatternCertificate c hc.1 hc.2⟩

noncomputable def certificateConstraints (n : Nat) : List (ColorPattern n) := by
  classical
  exact (Finset.univ.filter CertificateConstraint).toList

theorem mem_certificateConstraints {n : Nat} (c : ColorPattern n) :
    c ∈ certificateConstraints n ↔ CertificateConstraint c := by
  classical
  simp [certificateConstraints]

/-- An unconditional signed-join formula for the winning indicator. -/
theorem winning_signed_join_indicator {n : Nat} (r : ColorPattern n) :
    joinTermScore (certificateJoinTerms (certificateConstraints n)) r =
      if WinningColorPattern r then 1 else 0 := by
  classical
  apply certificateJoinTerms_winning_indicator
  intro p
  simp only [mem_certificateConstraints]
  exact winning_iff_constraint_refinement p

#print axioms winning_iff_constraint_refinement
#print axioms winning_signed_join_indicator
end LC004
