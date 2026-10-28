import LC004.ColorPatternSpace

namespace LC004

/-- A representation is an unlabeled noncrossing perfect matching and
an unordered choice of exactly two of its edges (equivalence classes). -/
abbrev FourfoldMatchingRepresentation (n : Nat) :=
  (p : {p : ColorPattern n // NoncrossingPairPattern p}) ×
    {chosen : Finset (Quotient p.val) // chosen.card = 2}

/-- Merge selected classes of an arbitrary partition; all other classes
remain separate. This is a relation on original positions, without any
chosen ordering or naming of the matching's edges. -/
def mergePatternClasses {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) : ColorPattern n where
  r i j := p i j ∨ (Quotient.mk p i ∈ chosen ∧ Quotient.mk p j ∈ chosen)
  iseqv := by
    refine ⟨fun i => Or.inl (p.refl i), ?_, ?_⟩
    · intro i j h
      rcases h with h | ⟨hi, hj⟩
      · exact Or.inl (p.symm h)
      · exact Or.inr ⟨hj, hi⟩
    · intro i j k hij hjk
      rcases hij with hij | ⟨hi, hj⟩
      · rcases hjk with hjk | ⟨hj, hk⟩
        · exact Or.inl (p.trans hij hjk)
        · exact Or.inr ⟨by simpa only [Quotient.sound hij] using hj, hk⟩
      · rcases hjk with hjk | ⟨_, hk⟩
        · exact Or.inr ⟨hi, by simpa only [Quotient.sound hjk] using hj⟩
        · exact Or.inr ⟨hi, hk⟩

def fourfoldRepresentationPattern {n : Nat}
    (r : FourfoldMatchingRepresentation n) : ColorPattern n :=
  mergePatternClasses r.1.val r.2.val

theorem mergePatternClasses_rel {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) (i j : Fin n) :
    mergePatternClasses p chosen i j ↔
      p i j ∨ (Quotient.mk p i ∈ chosen ∧ Quotient.mk p j ∈ chosen) := Iff.rfl

theorem mergePatternClasses_coarsens {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) {i j : Fin n} (h : p i j) :
    mergePatternClasses p chosen i j := Or.inl h

theorem winning_mergePatternClasses {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) (h : WinningColorPattern p) :
    WinningColorPattern (mergePatternClasses p chosen) := by
  obtain ⟨cert⟩ := h
  refine ⟨cert.recolor _ ?_⟩
  intro i j hij
  exact (patternColor_eq_iff _ i j).mpr
    (mergePatternClasses_coarsens p chosen ((patternColor_eq_iff p i j).mp hij))

/-- Actual finite domain for the fourfold matching-to-pattern map.
No Catalan cardinality or surjectivity is assumed here. -/
noncomputable def fourfoldMatchingRepresentationCount (n : Nat) : Nat := by
  classical
  exact Fintype.card (FourfoldMatchingRepresentation n)

#print axioms mergePatternClasses
#print axioms winning_mergePatternClasses

end LC004
