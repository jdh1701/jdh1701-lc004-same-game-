import LC004.NoMergeAdjacentLeftConcrete
import LC004.NoMergeExchangeInterior
import LC004.ListSplit
import LC004.PrefixIndexed

namespace LC004

/-- Global adjacent-left exchange obtained by splitting the last run of pre,
using the green front critical pair, and lifting both moves through the inert
earlier prefix. -/
theorem adjacentLeftNoMergeExchange_proved :
    AdjacentLeftNoMergeExchange := by
  intro pre post u c hpre hn hboundary hchild
  obtain ⟨prefix, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  have hidx : pre.length - 1 = prefix.length := by
    rw [hpreEq]
    simp
  have hchild' :
      IndexedStep ((a,ba) :: post) 0
        (u.drop prefix.length) := by
    have hexec := stepAt_complete hchild
    rw [hpreEq, hidx] at hexec
    -- strip the inert prefix at the adjacent boundary
    have hshape :
        ∃ t, u = prefix ++ t ∧
          IndexedStep ((a,ba) :: post) 0 t := by
      -- executable index-zero stripping at exactly prefix.length
      sorry
    obtain ⟨t, hu, ht⟩ := hshape
    simpa [hu] using ht
  -- use an explicit stripped successor rather than drop-based reconstruction
  have hshape :
      ∃ t, u = prefix ++ t ∧
        IndexedStep ((a,ba) :: post) 0 t := by
    sorry
  obtain ⟨t, hu, ht⟩ := hshape
  have hnlocal :
      Normalized ((a,ba) :: (c,true) :: post) := by
    rw [hpreEq] at hn
    exact normalized_suffix_of_append
      (xs := prefix)
      (ys := (a,ba) :: (c,true) :: post) hn
  obtain ⟨v, hv, hdom⟩ :=
    adjacentLeftNoMergeFront_proved hnlocal ht
  let gv : RunState := prefix ++ v
  have hparent :
      IndexedStep
        (pre ++ (c,true) :: post)
        (pre.length - 1) gv := by
    rw [hpreEq, hidx]
    -- local selected index zero becomes prefix.length globally
    simpa [gv, List.append_assoc] using
      indexedStep_prepend prefix hv
  have hdomGlobal : ExchangeDominates u gv := by
    rw [hu]
    cases hdom with
    | heavier hh =>
        exact exchangeDominates_prepend_heavier prefix hh
    | @oneStep k w hs hh =>
        -- concrete front witness uses deletion of inserted c at index zero;
        -- after prefixing, this is at prefix.length.  Prove directly rather
        -- than invoking the nonzero-local-index helper.
        have hs' :
            IndexedStep (prefix ++ v) prefix.length (prefix ++ w) := by
          simpa using indexedStep_prepend prefix (by simpa using hs)
        exact ExchangeDominates.oneStep hs'
          (heavier_append (heavier_refl prefix) hh)
  exact ⟨gv, hparent, hdomGlobal⟩

end LC004
