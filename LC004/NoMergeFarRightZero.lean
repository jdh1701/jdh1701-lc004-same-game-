import LC004.NoMergeExchangeInterior
import LC004.NoMergeExchangeLocal
import LC004.ExchangeDominance
import LC004.HeadColorLemmas

namespace LC004

/-- Boundary-zero dominance transport specialized to the far-right no-merge
configuration.  This is the sole remaining hole in the corrected far-right
reduction. -/
def FarRightZeroTransport : Prop :=
  ∀ {pre post u v w : RunState} {c : Nat},
    Normalized (pre ++ (c,true) :: post) →
    (∀ p q, pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) →
    IndexedStep v 0 w →
    Heavier u w →
    ExchangeDominates (pre ++ u) (pre ++ v)

/-- The zero-index case is expected to be discharged by inspecting the
left-edge exchange witness: either pre is empty, or the retained boundary
condition makes the prefixed deletion a legal no-merge move. -/
def FarRightZeroBoundaryLaw : Prop :=
  ∀ {pre v w : RunState},
    pre ≠ [] →
    IndexedStep v 0 w →
    (∀ p q, pre.getLast? = some p → v.head? = some q → p.1 ≠ q.1) →
    IndexedStep (pre ++ v) pre.length (pre ++ w)


/-- An indexed move at local index zero is necessarily deletion of the first
heavy run, hence has the exact shape `(d,true) :: w -> w`. -/
theorem indexedStep_zero_shape
    {v w : RunState}
    (h : IndexedStep v 0 w) :
    ∃ d : Nat, v = (d,true) :: w := by
  have he := stepAt_complete h
  cases v with
  | nil =>
      simp [stepAt] at he
  | cons x xs =>
      rcases x with ⟨d,b⟩
      cases b with
      | false =>
          simp [stepAt] at he
      | true =>
          simp [stepAt] at he
          subst w
          exact ⟨d, rfl⟩

/-- Lift a local index-zero deletion through a prefix when the newly exposed
boundary colors differ. -/
theorem indexedStep_prepend_zero_of_boundary
    (pre : RunState)
    {v w : RunState}
    (h : IndexedStep v 0 w)
    (hb : ∀ p q,
      pre.getLast? = some p →
      w.head? = some q →
      p.1 ≠ q.1) :
    IndexedStep (pre ++ v) pre.length (pre ++ w) := by
  obtain ⟨d, rfl⟩ := indexedStep_zero_shape h
  exact IndexedStep.noMerge
    (pre := pre) (post := w) (c := d) hb

end LC004
