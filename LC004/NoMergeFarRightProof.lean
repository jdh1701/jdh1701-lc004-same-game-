import LC004.NoMergeExchangeInterior
import LC004.NoMergeExchangeLocal
import LC004.PrefixIndexed
import LC004.NoMergeFarRightZero
import LC004.HeadColorLemmas

namespace LC004

/-- Far-right no-merge exchange: after stripping the prefix, insertion is on
the left of the suffix, so the correct local theorem is noMerge_exchange_left. -/
theorem farRightNoMergeExchange_proved :
    FarRightNoMergeExchange := by
  intro pre post u c i hn hboundary hi hchild
  obtain ⟨j, hij⟩ : ∃ j, i = pre.length + (j + 1) := by
    refine ⟨i - pre.length - 1, ?_⟩
    omega
  subst i
  obtain ⟨t, hu, ht⟩ :=
    indexedStep_strip_prefix pre post
      (i := j + 1) (by omega) hchild
  obtain ⟨v, hv, hdom⟩ :=
    noMerge_exchange_left (c := c) ht
  let parentV : RunState := pre ++ v
  have hp :
      IndexedStep
        (pre ++ ((c,true) :: post))
        (pre.length + ((j + 1) + 1))
        parentV := by
    have hlift :=
      indexedStep_prepend_list pre
        (i := (j + 1) + 1) (by omega) hv
    simpa [parentV, List.append_assoc] using hlift
  have hdom' : ExchangeDominates u parentV := by
    rw [hu]
    cases hdom with
    | heavier hh =>
        exact ExchangeDominates.heavier
          (heavier_append (heavier_refl pre) hh)
    | @oneStep k w hs hh =>
        by_cases hk : k = 0
        · subst k
          have hheadPostT :
              headColor? post = headColor? t :=
            indexedStep_nonzero_headColor (by omega) ht
          have hheadTW :
              headColor? t = headColor? w :=
            heavier_headColor hh
          have hheadPostW :
              headColor? post = headColor? w :=
            hheadPostT.trans hheadTW
          have hbw :
              ∀ p q,
                pre.getLast? = some p →
                w.head? = some q →
                p.1 ≠ q.1 :=
            boundary_of_headColor_eq hheadPostW hboundary
          have hs' :
              IndexedStep (pre ++ v) pre.length (pre ++ w) :=
            indexedStep_prepend_zero_of_boundary pre hs hbw
          exact ExchangeDominates.oneStep hs'
            (heavier_append (heavier_refl pre) hh)
        · exact exchangeDominates_prepend_oneStep pre hk hs hh
  refine ⟨parentV, ?_, hdom'⟩
  simpa [Nat.add_assoc] using hp

end LC004
