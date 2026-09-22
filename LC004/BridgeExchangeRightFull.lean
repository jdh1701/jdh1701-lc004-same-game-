import LC004.BridgeExchangeRight
import LC004.PrefixIndexed

namespace LC004

/-- General right-side bridge diamond.  A child move strictly to the right of
the newly merged run can be stripped past the inert prefix, exchanged in the
front-edge configuration, then lifted back through the same prefix. -/
theorem bridge_right_exchange
    {pre post u : RunState}
    {c d : Nat} {bp bq : Bool} {i : Nat}
    (hchild :
      IndexedStep
        (pre ++ (c,true) :: post)
        (pre.length + (i + 1))
        u) :
    ∃ v : RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        (pre.length + (i + 3))
        v ∧
      ExchangeTarget u v := by
  obtain ⟨t, hu, ht⟩ :=
    indexedStep_strip_prefix
      pre ((c,true) :: post) (i := i + 1) (by omega) hchild
  obtain ⟨v0, hp0, hs0⟩ :=
    bridge_front_right_exchange_step
      (post := post) (c := c) (d := d) (bp := bp) (bq := bq)
      ht
  have hp :=
    indexedStep_prepend_list pre (i := i + 3) (by omega) hp0
  have hs :=
    indexedStep_prepend_list pre (i := 1) (by omega) hs0
  subst u
  refine ⟨pre ++ v0, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hp
  · exact ExchangeTarget.oneStep (by simpa using hs)

end LC004
