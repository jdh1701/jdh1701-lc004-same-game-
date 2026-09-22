import LC004.NoMergeExchangeInterior
import LC004.NoMergeExchangeLocal
import LC004.ExchangeDominance

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

end LC004
