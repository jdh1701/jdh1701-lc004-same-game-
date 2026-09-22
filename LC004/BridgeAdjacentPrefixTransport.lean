import LC004.BridgeAdjacentLeftClosure
import LC004.ExchangeTarget
import LC004.PrefixIndexed
import LC004.HeavierLemmas

namespace LC004

/-- Prefix transport for exchange targets in the nonzero one-step case. -/
theorem exchangeTarget_prepend_nonzero
    (pre : RunState)
    {u v : RunState}
    (h : ExchangeTarget u v)
    (hnz : ∀ {i w}, IndexedStep v i w → i ≠ 0) :
    ExchangeTarget (pre ++ u) (pre ++ v) := by
  cases h with
  | same hv =>
      subst v
      exact ExchangeTarget.same rfl
  | heavier hh =>
      exact ExchangeTarget.heavier
        (heavier_append (heavier_refl pre) hh)
  | @oneStep i hs =>
      have hi : i ≠ 0 := hnz hs
      have hp :
          IndexedStep (pre ++ v) (pre.length + i) (pre ++ u) :=
        indexedStep_prepend_list pre hi hs
      exact ExchangeTarget.oneStep hp


end LC004
