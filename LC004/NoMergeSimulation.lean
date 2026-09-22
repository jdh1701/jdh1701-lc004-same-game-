import LC004.RunState
import LC004.HeavierLemmas
import LC004.SplitRunLemmas
import LC004.Transition

namespace LC004

/-- No-merge simulation when the deletion is at an endpoint (empty prefix or
empty suffix). These are the first formally isolated no-merge cases. -/
theorem deleteSimulation_noMerge_left
    {post : RunState} {c : Nat} {t : RunState}
    (h : Heavier ((c,true)::post) t) :
    ∃ v : RunState, Step t v ∧ Heavier post v := by
  obtain ⟨pre', post', e, ht, he, hpre, hpost⟩ :=
    heavier_split_run [] post c true h
  have hprenil : pre' = [] := by
    cases pre' <;> simp_all [Heavier]
  subst pre'
  have hetrue : e = true := by
    cases e <;> simp_all
  subst e
  rw [ht]
  refine ⟨post', ?_, hpost⟩
  exact Step.noMerge (by
    intro p q hp hq
    simp at hp)

theorem deleteSimulation_noMerge_right
    {pre : RunState} {c : Nat} {t : RunState}
    (h : Heavier (pre ++ [(c,true)]) t) :
    ∃ v : RunState, Step t v ∧ Heavier pre v := by
  obtain ⟨pre', post', e, ht, he, hpre, hpost⟩ :=
    heavier_split_run pre [] c true h
  have hpostnil : post' = [] := by
    cases post' <;> simp_all [Heavier]
  subst post'
  have hetrue : e = true := by
    cases e <;> simp_all
  subst e
  rw [ht]
  refine ⟨pre', ?_, hpre⟩
  exact Step.noMerge (by
    intro p q hp hq
    simp at hq)

end LC004
