import LC004.NoMergeExchangeInterior
import LC004.NoMergeExchangeRight
import LC004.PrefixIndexed

namespace LC004

/-- Far-right no-merge exchange reduces to the already-proved right-edge
exchange after stripping the unchanged prefix. -/
theorem farRightNoMergeExchange_proved :
    FarRightNoMergeExchange := by
  intro pre post u c i hn hi hchild
  obtain ⟨j, hij⟩ : ∃ j, i = pre.length + (j + 1) := by
    refine ⟨i - pre.length - 1, ?_⟩
    omega
  subst i
  obtain ⟨t, hu, ht⟩ :=
    indexedStep_strip_prefix pre post
      (i := j + 1) (by omega) hchild
  obtain ⟨v, hv, hdom⟩ :=
    noMerge_exchange_right (c := c) ht
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
        -- Right-edge exchange's compensating move deletes the appended heavy
        -- run, hence it is nonzero whenever the child had a legal move.
        have hk : k ≠ 0 := by
          intro hk0
          subst k
          have hlt := indexedStep_index_lt ht
          cases post with
          | nil => simp at hlt
          | cons z zs => omega
        exact exchangeDominates_prepend_oneStep pre hk hs hh
  refine ⟨parentV, ?_, hdom'⟩
  simpa [Nat.add_assoc] using hp

end LC004
