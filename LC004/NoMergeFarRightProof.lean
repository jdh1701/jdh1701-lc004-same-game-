import LC004.NoMergeExchangeInterior
import LC004.NoMergeExchangeRight
import LC004.PrefixIndexed

namespace LC004

/-- Far-right no-merge exchange reduces by stripping the unchanged prefix to
the already-proved right-edge exchange theorem. -/
theorem farRightNoMergeExchange_proved :
    FarRightNoMergeExchange := by
  intro pre post u c i hn hi hchild
  have hindex : ∃ j, i = pre.length + j + 1 := by
    refine ⟨i - pre.length - 1, ?_⟩
    omega
  obtain ⟨j, rfl⟩ := hindex
  have hchildIndex :
      pre.length + j + 1 = pre.length + (j + 1) := by omega
  have hstrip :
      ∃ t, u = pre ++ t ∧ IndexedStep post (j + 1) t := by
    apply indexedStep_strip_prefix pre post (i := j + 1)
    · omega
    · simpa [hchildIndex, Nat.add_assoc] using hchild
  obtain ⟨t, hu, ht⟩ := hstrip
  obtain ⟨v, hv, hdom⟩ :=
    noMerge_exchange_right (c := c) ht
  let parentV : RunState := pre ++ v
  have hp :
      IndexedStep
        (pre ++ (c,true) :: post)
        (pre.length + (j + 1) + 1)
        parentV := by
    have hlift :=
      indexedStep_prepend_list pre (i := j + 2) (by omega) hv
    simpa [parentV, List.append_assoc, Nat.add_assoc] using hlift
  have hdom' : ExchangeDominates u parentV := by
    rw [hu]
    cases hdom with
    | heavier hh =>
        exact ExchangeDominates.heavier
          (heavier_append (heavier_refl pre) hh)
    | @oneStep k w hs hh =>
        have hk : k ≠ 0 := by
          intro hk0
          subst k
          cases hs <;> simp
        exact exchangeDominates_prepend_oneStep pre hk hs hh
  exact ⟨parentV, hp, hdom'⟩

end LC004
