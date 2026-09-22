import LC004.RunState
import LC004.HeavierLemmas
import LC004.SplitRunLemmas
import LC004.Transition
import LC004.Simulation

namespace LC004

/-- First substantive concrete simulation theorem: merge-forming deletions are
simulated by the corresponding merge-forming deletion in every heavier state. -/
theorem deleteSimulation_merge
    {pre post : RunState} {c d : Nat} {bp bq : Bool} {t : RunState}
    (h :
      Heavier
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        t) :
    ∃ v : RunState,
      Step t v ∧
      Heavier (pre ++ (c,true) :: post) v := by
  obtain ⟨pre', tail', e, ht, he, hpre, htail⟩ :=
    heavier_split_run pre ((c,bq)::post) d true h
  have hetrue : e = true := by
    exact Bool.eq_true_iff.mpr (he rfl)
  subst e
  have htailshape :
      ∃ q post',
        tail' = (c,q)::post' ∧
        (bq → q) ∧ Heavier post post' := by
    simpa using (heavier_head_shape htail)
  obtain ⟨q, post', htailEq, hbq, hpost⟩ := htailshape
  subst tail'
  refine ⟨pre' ++ (c,true)::post', ?_, ?_⟩
  · rw [ht]
    exact Step.merge
  · exact heavier_append hpre (by
      simp only [Heavier]
      exact ⟨trivial, trivial, hpost⟩)

end LC004
