import LC004.RunState
import LC004.Transition
import LC004.NoMergeSimulation
import LC004.InteriorNoMerge
import LC004.ListSplit

namespace LC004

theorem deleteSimulation_noMerge_full
    {pre post : RunState} {c : Nat} {t : RunState}
    (hboundary : ∀ p q,
      pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1)
    (h : Heavier (pre ++ (c,true) :: post) t) :
    ∃ v : RunState, Step t v ∧ Heavier (pre ++ post) v := by
  by_cases hpre : pre = []
  · subst pre
    simpa using (deleteSimulation_noMerge_left (post := post) (c := c) h)
  · by_cases hpost : post = []
    · subst post
      simpa using (deleteSimulation_noMerge_right (pre := pre) (c := c) h)
    · obtain ⟨left, ⟨a,ba⟩, hpreEq, hpreLast⟩ :=
        exists_split_last pre hpre
      cases post with
      | nil => contradiction
      | cons rq right =>
          rcases rq with ⟨b,bb⟩
          have hab : a ≠ b := by
            exact hboundary (a,ba) (b,bb) hpreLast (by simp)
          rw [hpreEq] at h ⊢
          simpa using
            (deleteSimulation_noMerge_interior
              (left := left) (right := right)
              (a := a) (b := b) (c := c)
              (ba := ba) (bb := bb) hab h)

end LC004
