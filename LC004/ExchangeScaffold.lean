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

/-- A non-bridge deletion from a state with at least two runs leaves a
nonempty child. -/
theorem noMergeChoice_child_nonempty
    {s : RunState} {chosen : Nat × RunState}
    (hlen : 1 < s.length)
    (hnon : NoMergeChoice s chosen) :
    chosen.2 ≠ [] := by
  rcases hnon with ⟨pre, post, c, hboundary, hs, hch⟩
  subst s
  subst chosen
  intro hempty
  have hlen0 : (pre ++ post).length = 0 := by
    simpa using congrArg List.length hempty
  have hsum : pre.length + post.length = 0 := by
    simpa using hlen0
  have hpre0 : pre.length = 0 := Nat.eq_zero_of_add_eq_zero_left hsum
  have hpost0 : post.length = 0 := Nat.eq_zero_of_add_eq_zero_right hsum
  have hpre : pre = [] := List.length_eq_zero.mp hpre0
  have hpost : post = [] := List.length_eq_zero.mp hpost0
  subst pre
  subst post
  simp at hlen

/-- Conditional bridge-necessity theorem. The only remaining Same-Game-local
obligation is the concrete exchange lemma for successful no-merge choices. -/
theorem bridgeChoice_of_unique_and_noMerge_exchange
    {s : RunState} {chosen : Nat × RunState}
    (hlen : 1 < s.length)
    (hu : UniqueSuccessfulChoice s)
    (hchosen : SuccessfulChoice s chosen)
    (hexchange :
      ∀ {s ch}, NoMergeChoice s ch → SuccessfulChoice s ch →
        ChildChoicesLift s ch) :
    BridgeChoice s chosen := by
  rcases successfulChoice_classify hchosen with hnon | hbridge
  · have hchildne := noMergeChoice_child_nonempty hlen hnon
    exact (uniqueChoice_not_nonBridge_of_exchange
      hu hchosen hnon hchildne hexchange).elim
  · exact hbridge


end LC004
