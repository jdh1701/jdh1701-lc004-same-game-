import LC004.BridgeExchangeFarLeft
import LC004.SuffixIndexed
import LC004.ExecutableCorrespondence

namespace LC004

/-- Concrete far-left bridge context theorem.  A move strictly inside the
prefix is unaffected by replacing the bridge tail; both parent and child
successors share the transformed prefix, so the bridge exchange target is
obtained by the same local move. -/
def BridgeFarLeftConcreteTarget : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {i : Nat} {u : RunState},
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    i + 1 < pre.length →
    IndexedStep (pre ++ (c,true) :: post) i u →
    ∃ pre' : RunState,
      IndexedStep pre i pre' ∧
      u = pre' ++ (c,true) :: post ∧
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        i
        (pre' ++ (c,bp) :: (d,true) :: (c,bq) :: post)

/-- This stronger context theorem is sufficient for BridgeFarLeftContextLaw:
delete the bridge middle run after the lifted prefix move to reach the child
successor exactly. -/
theorem bridgeFarLeftContext_of_concrete
    (h : BridgeFarLeftConcreteTarget) :
    BridgeFarLeftContextLaw := by
  intro pre post c d bp bq i u hn hi hchild
  obtain ⟨pre', hpre, hu, hparent⟩ := h hn hi hchild
  let v : RunState :=
    pre' ++ (c,bp) :: (d,true) :: (c,bq) :: post
  have hbridge :
      IndexedStep v (pre'.length + 1)
        (pre' ++ (c,true) :: post) := by
    simpa [v] using
      (IndexedStep.merge
        (pre := pre') (post := post)
        (c := c) (d := d) (bp := bp) (bq := bq))
  refine ⟨v, ?_, Or.inr ?_⟩
  · simpa [v] using hparent
  · refine ⟨pre'.length + 1, ?_⟩
    rw [hu]
    exact hbridge

end LC004
