import LC004.NoMergeExchangeInterior
import LC004.ListSplit
import LC004.NoMergeAdjacentLeftConcrete
import LC004.ExchangeDominance
import LC004.ExecutableCorrespondence

namespace LC004

/-- Boundary-aware adjacent-left critical pair.  This deliberately keeps the
run immediately before the selected run visible, because deleting the selected
run may merge across that boundary. -/
def AdjacentLeftBoundaryLocal : Prop :=
  ∀ {x a c : Nat} {bx ba : Bool} {post u : RunState},
    Normalized ((x,bx) :: (a,ba) :: (c,true) :: post) →
    IndexedStep ((x,bx) :: (a,ba) :: post) 1 u →
    ∃ v : RunState,
      IndexedStep ((x,bx) :: (a,ba) :: (c,true) :: post) 1 v ∧
      ExchangeDominates u v

/-- If the earlier context is empty, the already-green front theorem closes
the adjacent-left case.  Otherwise only AdjacentLeftBoundaryLocal is needed;
all still-earlier runs are inert because the selected local index is one. -/
theorem adjacentLeftNoMergeExchange_reduces_to_boundary
    (hboundaryLocal : AdjacentLeftBoundaryLocal) :
    AdjacentLeftNoMergeExchange := by
  intro pre post u c hpre hn hboundary hchild
  obtain ⟨ctx, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  cases ctx with
  | nil =>
      have hnlocal : Normalized ((a,ba) :: (c,true) :: post) := by
        simpa [hpreEq] using hn
      have hc : IndexedStep ((a,ba) :: post) 0 u := by
        simpa [hpreEq] using hchild
      simpa [hpreEq] using
        (adjacentLeftNoMergeFront_proved hnlocal hc)
  | cons x xs =>
      -- expose the last run of the earlier context as well
      obtain ⟨front, penult, hctxEq, hctxLast⟩ :=
        exists_split_last (x :: xs) (by simp)
      rcases penult with ⟨d,bd⟩
      have hnlocal :
          Normalized ((d,bd) :: (a,ba) :: (c,true) :: post) := by
        rw [hpreEq, hctxEq] at hn
        have hn' :
            Normalized
              (front ++ ((d,bd) :: (a,ba) :: (c,true) :: post)) := by
          simpa [List.append_assoc] using hn
        exact normalized_suffix_of_append
          (xs := front)
          (ys := (d,bd) :: (a,ba) :: (c,true) :: post) hn'
      -- The remaining global lifting is safe at local index one.
      -- Strip/lift through front using the existing nonzero prefix machinery.
      have hidx : pre.length - 1 = front.length + 1 := by
        rw [hpreEq, hctxEq]
        simp
      have hchildLocal :
          ∃ t, u = front ++ t ∧
            IndexedStep ((d,bd) :: (a,ba) :: post) 1 t := by
        rw [hidx] at hchild
        have hc :
            IndexedStep
              (front ++ ((d,bd) :: (a,ba) :: post))
              (front.length + 1) u := by
          simpa [hpreEq, hctxEq, List.append_assoc] using hchild
        exact indexedStep_strip_prefix front
          ((d,bd) :: (a,ba) :: post) (by omega) hc
      obtain ⟨t, hu, ht⟩ := hchildLocal
      obtain ⟨v, hv, hdom⟩ := hboundaryLocal hnlocal ht
      let gv := front ++ v
      have hp :
          IndexedStep
            (pre ++ (c,true) :: post)
            (pre.length - 1) gv := by
        have hl := indexedStep_prepend_list front (by omega) hv
        simpa [hpreEq, hctxEq, hidx, gv, List.append_assoc] using hl
      have hd : ExchangeDominates u gv := by
        rw [hu]
        cases hdom with
        | heavier hh =>
            exact exchangeDominates_prepend_heavier front hh
        | @oneStep k w hs hh =>
            have hk : k ≠ 0 := by
              intro hk0
              subst k
              -- The boundary-aware local theorem's compensating moves occur
              -- at index one; an index-zero witness is impossible here.
              cases hs <;> simp at *
            exact exchangeDominates_prepend_oneStep front hk hs hh
      exact ⟨gv, hp, hd⟩

end LC004
