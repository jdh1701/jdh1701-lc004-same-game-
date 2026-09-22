import LC004.RunState
import LC004.Transition
import LC004.Simulation
import LC004.DeleteSimulation
import LC004.NoMergeSimulation
import LC004.InteriorNoMerge

namespace LC004

/-- Full concrete forward simulation for normalized one-dimensional Same Game. -/
theorem deleteSimulation_full : DeleteSimulation := by
  intro s t u hst hstep
  cases hstep with
  | merge =>
      exact deleteSimulation_merge hst
  | noMerge hboundary =>
      cases pre with
      | nil =>
          simpa using (deleteSimulation_noMerge_left (post := post) (c := c) hst)
      | cons lp lps =>
          cases post with
          | nil =>
              simpa using
                (deleteSimulation_noMerge_right
                  (pre := (lp::lps)) (c := c) hst)
          | cons rq rqs =>
              rcases lp with ⟨a,ba⟩
              rcases rq with ⟨b,bb⟩
              have hab : a ≠ b := by
                apply hboundary (a,ba) (b,bb)
                · simp
                · simp
              simpa [List.cons_append] using
                (deleteSimulation_noMerge_interior
                  (left := lps) (right := rqs)
                  (a := a) (b := b) (c := c)
                  (ba := ba) (bb := bb) hab hst)

/-- Unconditional Same-Game solvability monotonicity, obtained by instantiating
the already verified generic simulation theorem with deleteSimulation_full. -/
theorem sameGame_solvable_mono_full
    {s t : RunState}
    (hst : Heavier s t)
    (hs : Solvable Step (fun x => x = []) s) :
    Solvable Step (fun x => x = []) t := by
  exact sameGame_solvable_mono deleteSimulation_full hst hs

end LC004
