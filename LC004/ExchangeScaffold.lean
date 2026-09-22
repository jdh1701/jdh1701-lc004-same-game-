import LC004.SuccessfulPaths
import LC004.MoveClassification

namespace LC004

/-- Every nonempty solvable state has at least one successful indexed first
choice. -/
theorem runSolvable_nonempty_has_successfulChoice
    {s : RunState}
    (hne : s ≠ [])
    (hsol : RunSolvable s) :
    ∃ ch : Nat × RunState, SuccessfulChoice s ch := by
  cases hsol with
  | done ht =>
      exact (hne ht).elim
  | @move s t hstep htail =>
      obtain ⟨i, hi⟩ := step_has_index hstep
      exact ⟨(i,t), hi, htail⟩

/-- A unique successful first choice excludes every distinct successful
alternative. -/
theorem uniqueSuccessfulChoice_no_alt
    {s : RunState} {chosen alt : Nat × RunState}
    (hu : UniqueSuccessfulChoice s)
    (hchosen : SuccessfulChoice s chosen)
    (halt : SuccessfulChoice s alt)
    (hne : alt ≠ chosen) :
    False := by
  rcases hu with ⟨u, huok, huuniq⟩
  have h1 : chosen = u := huuniq chosen hchosen
  have h2 : alt = u := huuniq alt halt
  exact hne (h2.trans h1.symm)

/-- Exchange property for a parent choice: every successful first choice of
its child can be lifted to a distinct successful first choice of the parent. -/
def ChildChoicesLift
    (s : RunState) (chosen : Nat × RunState) : Prop :=
  ∀ childChoice : Nat × RunState,
    SuccessfulChoice chosen.2 childChoice →
      ∃ alt : Nat × RunState,
        SuccessfulChoice s alt ∧ alt ≠ chosen

/-- Under a unique successful parent choice, a nonempty successful child
cannot satisfy unrestricted exchange: its next successful move would create
a second successful parent choice. -/
theorem uniqueChoice_forbids_full_child_exchange
    {s : RunState} {chosen : Nat × RunState}
    (hu : UniqueSuccessfulChoice s)
    (hchosen : SuccessfulChoice s chosen)
    (hchildne : chosen.2 ≠ [])
    (hlift : ChildChoicesLift s chosen) :
    False := by
  obtain ⟨childChoice, hchild⟩ :=
    runSolvable_nonempty_has_successfulChoice hchildne hchosen.2
  obtain ⟨alt, halt, hne⟩ := hlift childChoice hchild
  exact uniqueSuccessfulChoice_no_alt hu hchosen halt hne

/-- This is the precise interface needed for bridge necessity. Once the
concrete local theorem says every successful non-bridge choice has full child
exchange, uniqueness rules such a choice out whenever its child is nonempty. -/
theorem uniqueChoice_not_nonBridge_of_exchange
    {s : RunState} {chosen : Nat × RunState}
    (hu : UniqueSuccessfulChoice s)
    (hchosen : SuccessfulChoice s chosen)
    (hnon : NoMergeChoice s chosen)
    (hchildne : chosen.2 ≠ [])
    (hexchange :
      ∀ {s ch}, NoMergeChoice s ch → SuccessfulChoice s ch →
        ChildChoicesLift s ch) :
    False := by
  exact uniqueChoice_forbids_full_child_exchange
    hu hchosen hchildne (hexchange hnon hchosen)

end LC004
