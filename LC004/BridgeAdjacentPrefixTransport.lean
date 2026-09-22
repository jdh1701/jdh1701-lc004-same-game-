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

/-- The concrete adjacent-left diamond produced in this development has its
compensating bridge merge at index one, hence it transports through arbitrary
prefixes. -/
theorem bridgeAdjacentLeftPrefixTransport_for_front
    {pre : RunState}
    {a c d : Nat} {ba bp bq : Bool}
    {post u v : RunState}
    (hn : Normalized
      ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post))
    (hchild : IndexedStep ((a,ba) :: (c,true) :: post) 0 u)
    (hparent :
      IndexedStep
        ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) 0 v)
    (ht : ExchangeTarget u v) :
    ExchangeTarget (pre ++ u) (pre ++ v) := by
  cases ht with
  | same hv =>
      subst v
      exact ExchangeTarget.same rfl
  | heavier hh =>
      exact ExchangeTarget.heavier
        (heavier_append (heavier_refl pre) hh)
  | @oneStep i hs =>
      have hi : i ≠ 0 := by
        intro hiz
        subst i
        have hlen := indexedStep_length_lt hs
        -- In the front bridge diamond, index zero was already the selected
        -- adjacent-left deletion; the compensating bridge merge is distinct.
        have hdet := indexedStep_target_unique hparent hs
        subst u
        have hnormParent := indexedStep_normalized hn hparent
        exact (by
          have := normalized_heavier hnormParent (heavier_refl v)
          simp at this)
      exact ExchangeTarget.oneStep
        (indexedStep_prepend_list pre hi hs)

end LC004
