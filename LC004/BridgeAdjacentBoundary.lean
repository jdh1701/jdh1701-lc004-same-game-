import LC004.BridgeExchangeRemaining
import LC004.BridgeExchangeLeftAssembly
import LC004.BridgeExchangeFarLeft
import LC004.BridgeFarLeftProof
import LC004.ExchangeTarget
import LC004.ExecutableCorrespondence

namespace LC004

/-- Boundary-aware local adjacent-left bridge pair.  The run x immediately
before the selected a-run is retained so that a child-side boundary merge
x=c is represented explicitly rather than hidden by invalid prefix transport. -/
def BridgeAdjacentLeftBoundaryLocal : Prop :=
  ∀ {x a c d : Nat} {bx ba bp bq : Bool}
    {post u : RunState},
    Normalized
      ((x,bx) :: (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) →
    IndexedStep ((x,bx) :: (a,ba) :: (c,true) :: post) 1 u →
    ∃ v : RunState,
      IndexedStep
        ((x,bx) :: (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        1 v ∧
      ExchangeTarget u v

/-- Concrete boundary-aware bridge critical pair. -/
theorem bridgeAdjacentLeftBoundaryLocal_proved :
    BridgeAdjacentLeftBoundaryLocal := by
  intro x a c d bx ba bp bq post u hn hchild
  have hba : ba = true := by
    have he := stepAt_complete hchild
    cases ba <;> simp [stepAt] at he ⊢
  subst ba
  have hxa : x ≠ a := by
    simpa [Normalized] using hn.1
  by_cases hxc : x = c
  · subst c
    have hu : u = (x,true) :: post := by
      have he := stepAt_complete hchild
      simpa [stepAt] using he.symm
    subst u
    let v : RunState :=
      (x,true) :: (d,true) :: (x,bq) :: post
    have hp :
        IndexedStep
          ((x,bx) :: (a,true) :: (x,bp) :: (d,true) :: (x,bq) :: post)
          1 v := by
      apply stepAt_sound
      simp [v, stepAt]
    have hs :
        IndexedStep v 1 ((x,true) :: post) := by
      simpa [v] using
        (IndexedStep.merge
          (pre := []) (post := post)
          (c := x) (d := d) (bp := true) (bq := bq))
    exact ⟨v, hp, ExchangeTarget.oneStep hs⟩
  · have hu : u = (x,bx) :: (c,true) :: post := by
      have he := stepAt_complete hchild
      simpa [stepAt, hxc] using he.symm
    subst u
    let v : RunState :=
      (x,bx) :: (c,bp) :: (d,true) :: (c,bq) :: post
    have hp :
        IndexedStep
          ((x,bx) :: (a,true) :: (c,bp) :: (d,true) :: (c,bq) :: post)
          1 v := by
      apply stepAt_sound
      simp [v, stepAt, hxc]
    have hs :
        IndexedStep v 2 ((x,bx) :: (c,true) :: post) := by
      simpa [v] using
        (IndexedStep.merge
          (pre := [(x,bx)]) (post := post)
          (c := c) (d := d) (bp := bp) (bq := bq))
    exact ⟨v, hp, ExchangeTarget.oneStep hs⟩

end LC004
