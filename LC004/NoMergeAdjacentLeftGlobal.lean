import LC004.NoMergeAdjacentLeftConcrete
import LC004.NoMergeExchangeInterior
import LC004.ListSplit
import LC004.PrefixIndexed

namespace LC004

/-- The only remaining adjacent-left bookkeeping fact: stripping an inert
ctx at exactly its length exposes the local index-zero move. -/
def AdjacentLeftIndexZeroStrip : Prop :=
  ∀ {ctx s u : RunState},
    IndexedStep (ctx ++ s) ctx.length u →
    ∃ t, u = ctx ++ t ∧ IndexedStep s 0 t

/-- Once index-zero stripping is available, the already-green front critical
pair can be lifted to the global adjacent-left interface. -/
theorem adjacentLeftNoMergeExchange_of_strip
    (hstrip : AdjacentLeftIndexZeroStrip) :
    AdjacentLeftNoMergeExchange := by
  intro pre post u c hpre hn hboundary hchild
  obtain ⟨ctx, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  have hidx : pre.length - 1 = ctx.length := by
    rw [hpreEq]
    simp
  rw [hidx] at hchild
  have hchild0 :
      IndexedStep (ctx ++ ((a,ba) :: post)) ctx.length u := by
    simpa [hpreEq, List.append_assoc] using hchild
  obtain ⟨t, hu, ht⟩ := hstrip hchild0
  have hnlocal :
      Normalized ((a,ba) :: (c,true) :: post) := by
    rw [hpreEq] at hn
    simpa [List.append_assoc] using
      (normalized_suffix_of_append
        (xs := ctx)
        (ys := (a,ba) :: (c,true) :: post) hn)
  obtain ⟨v, hv, hdom⟩ :=
    adjacentLeftNoMergeFront_proved hnlocal ht
  let gv : RunState := ctx ++ v
  have hparent :
      IndexedStep
        (pre ++ (c,true) :: post)
        (pre.length - 1) gv := by
    rw [hpreEq]
    simp only [List.length_append, List.length_singleton]
    have hlift := indexedStep_prepend ctx (by omega) hv
    simpa [gv, List.append_assoc] using hlift
  have hdomGlobal : ExchangeDominates u gv := by
    rw [hu]
    cases hdom with
    | heavier hh =>
        exact exchangeDominates_prepend_heavier ctx hh
    | @oneStep k w hs hh =>
        have hs' :
            IndexedStep (ctx ++ v) (ctx.length + k) (ctx ++ w) := by
          by_cases hk : k = 0
          · subst k
            simpa using indexedStep_prepend ctx (by omega) hs
          · exact indexedStep_prepend_list ctx hk hs
        exact ExchangeDominates.oneStep hs'
          (heavier_append (heavier_refl ctx) hh)
  exact ⟨gv, hparent, hdomGlobal⟩

end LC004
