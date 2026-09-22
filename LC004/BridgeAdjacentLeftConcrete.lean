import LC004.BridgeAdjacentLeftFront
import LC004.ExecutableCorrespondence

namespace LC004

/-- Concrete front adjacent-left critical pair.  Deleting the left run in the
child and in the parent is executable at index zero; the resulting states are
then compared by ExchangeTarget. -/
theorem bridge_adjacent_left_front_case
    {a c d : Nat} {ba bp bq : Bool}
    {post u : RunState}
    (hn : Normalized
      ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post))
    (hchild : IndexedStep ((a,ba) :: (c,true) :: post) 0 u) :
    ∃ v : RunState,
      IndexedStep
        ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        0 v ∧
      ExchangeTarget u v := by
  have hba : ba = true := by
    have hexec := stepAt_complete hchild
    cases ba <;> simp [stepAt] at hexec ⊢
  subst ba
  have hac : a ≠ c := by
    simpa [Normalized] using hn.1
  have hu : u = (c,true) :: post := by
    have hexec := stepAt_complete hchild
    simpa [stepAt] using hexec.symm
  subst u
  let v : RunState := (c,bp) :: (d,true) :: (c,bq) :: post
  have hp :
      IndexedStep
        ((a,true) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        0 v := by
    apply stepAt_sound
    simp [v, stepAt]
  have hs :
      IndexedStep v 1 ((c,true) :: post) := by
    simpa [v] using
      (IndexedStep.merge
        (pre := []) (post := post)
        (c := c) (d := d) (bp := bp) (bq := bq))
  exact ⟨v, hp, ExchangeTarget.oneStep hs⟩

end LC004
