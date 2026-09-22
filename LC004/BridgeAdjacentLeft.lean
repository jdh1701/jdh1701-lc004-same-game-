import LC004.BridgeExchangeLeftAssembly
import LC004.ExecutableCorrespondence
import LC004.ExchangeTarget

namespace LC004

/-- Local adjacent-left bridge critical pair.  The global prefix has been
stripped; the child move deletes the run immediately left of the merged run.
This is the last genuinely local bridge configuration. -/
def BridgeAdjacentLeftLocal : Prop :=
  ∀ {a c d : Nat} {ba bp bq : Bool}
    {leftTail post u : RunState},
    Normalized
      (leftTail ++ (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) →
    IndexedStep
      (leftTail ++ (a,ba) :: (c,true) :: post)
      leftTail.length u →
    ∃ v : RunState,
      IndexedStep
        (leftTail ++ (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        leftTail.length v ∧
      ExchangeTarget u v

/-- The local adjacent-left critical pair lifts directly to the global
adjacent-left structural interface. -/
theorem bridgeAdjacentLeftStructural_of_local
    (hlocal : BridgeAdjacentLeftLocal) :
    BridgeAdjacentLeftStructuralExchange := by
  intro pre post c d bp bq u hpre hn hchild
  obtain ⟨leftTail, last, hpreEq⟩ := exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  rw [hpreEq] at hn hchild ⊢
  have hidx :
      (leftTail ++ [(a,ba)]).length - 1 = leftTail.length := by
    simp
  rw [hidx] at hchild
  obtain ⟨v, hp, ht⟩ :=
    hlocal hn hchild
  refine ⟨(leftTail.length, v), hp, ?_, ht⟩
  simp
  omega

end LC004
