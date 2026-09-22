import LC004.RunState
import LC004.HeavierLemmas
import LC004.SplitRunLemmas
import LC004.Transition
import LC004.Simulation

namespace LC004

theorem deleteSimulation_merge
    {pre post : RunState} {c d : Nat} {bp bq : Bool} {t : RunState}
    (h :
      Heavier
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        t) :
    ∃ v : RunState,
      Step t v ∧
      Heavier (pre ++ (c,true) :: post) v := by
  obtain ⟨pre1, tail1, ep, ht1, hbp, hpre, hrest⟩ :=
    heavier_split_run pre ((d,true)::(c,bq)::post) c bp h
  obtain ⟨pre2, tail2, ed, ht2, hed, hmid, hrest2⟩ :=
    heavier_split_run [] ((c,bq)::post) d true hrest
  have hedtrue : ed = true := by
    cases ed <;> simp_all
  subst ed
  obtain ⟨q, post', htail, hbq, hpost⟩ :=
    heavier_head_shape hrest2
  subst tail2
  have hmidnil : pre2 = [] := by
    cases pre2 <;> simp_all [Heavier]
  subst pre2
  subst tail1
  rw [ht1]
  refine ⟨pre1 ++ (c,true)::post', ?_, ?_⟩
  · exact Step.merge
  · apply heavier_append hpre
    simp only [Heavier]
    exact ⟨trivial, (by intro _; trivial), hpost⟩

end LC004
