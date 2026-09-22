import LC004.SuccessfulPaths
import LC004.MoveClassification
import LC004.IndexedDeterminism

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
  have hz : pre.length = 0 ∧ post.length = 0 := Nat.add_eq_zero.mp hsum
  have hpre0 : pre.length = 0 := hz.1
  have hpost0 : post.length = 0 := hz.2
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


/-- For a bridge parent, every successful child choice except the newly
merged run can be lifted to a distinct successful first choice of the parent. -/
def BridgeChildChoicesLiftExceptMerged
    (pre post : RunState) (c d : Nat) (bp bq : Bool) : Prop :=
  ∀ childChoice : Nat × RunState,
    SuccessfulChoice (pre ++ (c,true) :: post) childChoice →
    childChoice.1 ≠ pre.length →
      ∃ alt : Nat × RunState,
        SuccessfulChoice
          (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) alt ∧
        alt ≠ (pre.length + 1, pre ++ (c,true) :: post)

/-- Conditional bridge heredity.  Once the concrete bridge-exchange lemma is
proved, the successful child of a unique bridge choice has a unique successful
first choice of its own. -/
theorem bridge_child_unique_of_exchange
    {pre post : RunState} {c d : Nat} {bp bq : Bool}
    (hmain :
      SuccessfulChoice
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        (pre.length + 1, pre ++ (c,true) :: post))
    (hparent :
      UniqueSuccessfulChoice
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post))
    (hlift : BridgeChildChoicesLiftExceptMerged pre post c d bp bq) :
    UniqueSuccessfulChoice (pre ++ (c,true) :: post) := by
  have hchildne : pre ++ (c,true) :: post ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
  obtain ⟨witness, hwitness⟩ :=
    runSolvable_nonempty_has_successfulChoice hchildne hmain.2
  have hwidx : witness.1 = pre.length := by
    by_contra hne
    obtain ⟨alt, halt, hnealt⟩ := hlift witness hwitness hne
    exact (uniqueSuccessfulChoice_no_alt hparent hmain halt hnealt).elim
  refine ⟨witness, hwitness, ?_⟩
  intro other hother
  have hoidx : other.1 = pre.length := by
    by_contra hne
    obtain ⟨alt, halt, hnealt⟩ := hlift other hother hne
    exact (uniqueSuccessfulChoice_no_alt hparent hmain halt hnealt).elim
  exact successfulChoice_eq_of_index_eq
    hwitness hother (hwidx.trans hoidx.symm)

end LC004
