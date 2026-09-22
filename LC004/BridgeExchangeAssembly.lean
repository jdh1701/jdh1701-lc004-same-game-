import LC004.ConditionalMain
import LC004.ExchangeScaffold
import LC004.BridgeExchangeRightFull
import LC004.NormalizedStepTarget

namespace LC004

/-- Structural bridge-exchange target, separated from solvability and
uniqueness bookkeeping.  The merged child run is at index pre.length; every
other child move must lift to a distinct parent move with a solvable-equivalent
exchange target. -/
def NormalizedBridgeStructuralExchange : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {childChoice : Nat × RunState},
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    IndexedStep
      (pre ++ (c,true) :: post)
      childChoice.1 childChoice.2 →
    childChoice.1 ≠ pre.length →
    ∃ alt : Nat × RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        alt.1 alt.2 ∧
      alt.1 ≠ pre.length + 1 ∧
      ExchangeTarget childChoice.2 alt.2

/-- The structural bridge law is exactly enough to discharge the semantic
bridge interface used by the final induction. -/
theorem normalizedBridgeExchange_of_structural
    (hstruct : NormalizedBridgeStructuralExchange) :
    LC004.NormalizedBridgeExchange := by
  intro pre post c d bp bq hn
  intro childChoice hchild hnotMerged
  obtain ⟨alt, halt, hne, htarget⟩ :=
    hstruct hn hchild.1 hnotMerged
  refine ⟨alt, ?_, ?_⟩
  · exact ⟨halt, exchangeTarget_solvable htarget hchild.2⟩
  · intro heq
    have hi := congrArg Prod.fst heq
    exact hne hi

/-- The already-proved arbitrary-prefix right bridge diamond supplies the
entire right-of-merged-run branch of the structural bridge law. -/
theorem bridgeStructuralExchange_right
    {pre post u : RunState}
    {c d : Nat} {bp bq : Bool} {i : Nat}
    (hchild :
      IndexedStep
        (pre ++ (c,true) :: post)
        (pre.length + (i + 1))
        u) :
    ∃ alt : Nat × RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        alt.1 alt.2 ∧
      alt.1 ≠ pre.length + 1 ∧
      ExchangeTarget u alt.2 := by
  obtain ⟨v, hp, ht⟩ :=
    bridge_right_exchange
      (pre := pre) (post := post)
      (c := c) (d := d) (bp := bp) (bq := bq)
      hchild
  refine ⟨(pre.length + (i + 3), v), hp, ?_, ht⟩
  omega

end LC004
