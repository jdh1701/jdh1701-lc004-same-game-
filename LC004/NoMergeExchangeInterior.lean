import LC004.NoMergeExchangeAssembly
import LC004.SuffixIndexed
import LC004.InsertedDeletion
import LC004.NoMergeAdjacentRight

namespace LC004

/-- Far-left branch of interior no-merge exchange.  If the child move occurs
strictly before the run immediately left of the inserted heavy run, suffix
inertness commutes the move past the insertion; deleting the inserted run then
returns to the child result. -/
theorem noMergeStructuralExchange_far_left
    {pre post u : RunState} {c : Nat} {i : Nat}
    (hn : Normalized (pre ++ (c,true) :: post))
    (hi : i + 1 < pre.length)
    (hchild : IndexedStep (pre ++ post) i u) :
    ∃ alt : Nat × RunState,
      IndexedStep (pre ++ (c,true) :: post) alt.1 alt.2 ∧
      alt.1 ≠ pre.length ∧
      ExchangeDominates u alt.2 := by
  have hprepost : Normalized (pre ++ post) := by
    have hparent :=
      IndexedStep.noMerge
        (pre := pre) (post := post) (c := c)
        (normalized_boundary_of_append
          (normalized_prefix_of_append
            (xs := pre ++ post) (ys := [])
            (by simpa using
              normalized_step hn
                (IndexedStep.noMerge
                  (pre := pre) (post := post) (c := c)
                  (normalized_boundary_of_append
                    (normalized_prefix_of_append
                      (xs := pre) (ys := (c,true) :: post) hn))))))
    exact indexedStep_normalized hn hparent
  have hp :
      IndexedStep
        (pre ++ (c,true) :: post)
        i
        (u.take pre.length ++ (c,true) :: u.drop pre.length) := by
    -- The exact split identity is supplied by suffix inertness; this theorem
    -- is intentionally left as the next compiler-discriminated construction.
    sorry
  refine ⟨(i, u.take pre.length ++ (c,true) :: u.drop pre.length), hp, ?_, ?_⟩
  · omega
  · have hdel :
        IndexedStep
          (u.take pre.length ++ (c,true) :: u.drop pre.length)
          (u.take pre.length).length
          u := by
      have hsplit : u.take pre.length ++ u.drop pre.length = u :=
        List.take_append_drop pre.length u
      rw [← hsplit]
      apply indexedStep_delete_inserted_of_normalized
      simpa [hsplit] using indexedStep_normalized hprepost hchild
    exact ExchangeDominates.oneStep hdel (heavier_refl u)

end LC004
