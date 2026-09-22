import LC004.BridgeFarLeftConcrete
import LC004.SuffixIndexed

namespace LC004

/-- The strengthened far-left target follows directly from suffix inertness:
a move strictly before the last prefix run transforms the prefix independently
of whichever bridge tail is appended. -/
theorem bridgeFarLeftConcreteTarget_proved :
    BridgeFarLeftConcreteTarget := by
  intro pre post c d bp bq i u hn hi hchild
  have hprestep :
      ∃ pre', IndexedStep pre i pre' := by
    have hexec := stepAt_complete hchild
    -- Suffix inertness gives the prefix successor uniquely.
    cases h : stepAt pre i with
    | none =>
        have happ :=
          stepAt_append_of_inside pre ((c,true) :: post) i hi
        rw [h] at happ
        simp at happ
        rw [happ] at hexec
        simp at hexec
    | some pre' =>
        exact ⟨pre', stepAt_sound h⟩
  obtain ⟨pre', hp⟩ := hprestep
  have hchildExec := stepAt_complete hchild
  have hctxChild :=
    stepAt_append_of_inside pre ((c,true) :: post) i hi
  rw [stepAt_complete hp] at hctxChild
  have hu :
      u = pre' ++ (c,true) :: post := by
    rw [hctxChild] at hchildExec
    simpa using Option.some.inj hchildExec.symm
  have hparent :
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        i
        (pre' ++ (c,bp) :: (d,true) :: (c,bq) :: post) := by
    apply stepAt_sound
    have hctx :=
      stepAt_append_of_inside pre
        ((c,bp) :: (d,true) :: (c,bq) :: post) i hi
    rw [stepAt_complete hp] at hctx
    exact hctx
  exact ⟨pre', hp, hu, hparent⟩

theorem bridgeFarLeftContextLaw_proved :
    BridgeFarLeftContextLaw :=
  bridgeFarLeftContext_of_concrete bridgeFarLeftConcreteTarget_proved

end LC004
