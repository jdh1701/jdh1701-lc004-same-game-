import LC004.IndexedMove

namespace LC004

/-- A first-move choice remembers both the selected run index and its successor. -/
def SuccessfulChoice (s : RunState) (ch : Nat × RunState) : Prop :=
  IndexedStep s ch.1 ch.2 ∧ RunSolvable ch.2

/-- A complete successful reduction path, with every selected run index retained. -/
inductive CompletePath : RunState → List (Nat × RunState) → Prop
  | done : CompletePath [] []
  | move {s t : RunState} {i : Nat} {rest : List (Nat × RunState)}
      (hstep : IndexedStep s i t)
      (htail : CompletePath t rest) :
      CompletePath s ((i, t) :: rest)

def UniqueSuccessfulFirst (s : RunState) : Prop :=
  ∃! ch : Nat × RunState, SuccessfulChoice s ch

def UniqueCompletePath (s : RunState) : Prop :=
  ∃! p : List (Nat × RunState), CompletePath s p

theorem completePath_solvable
    {s : RunState} {p : List (Nat × RunState)}
    (h : CompletePath s p) :
    RunSolvable s := by
  induction h with
  | done =>
      exact Solvable.done rfl
  | move hstep htail ih =>
      exact Solvable.move (indexedStep_forget hstep) ih

theorem solvable_completePath
    {s : RunState}
    (h : RunSolvable s) :
    ∃ p : List (Nat × RunState), CompletePath s p := by
  induction h with
  | @done s hs =>
      subst s
      exact ⟨[], CompletePath.done⟩
  | @move s t hstep hsol ih =>
      obtain ⟨i, hi⟩ := step_has_index hstep
      obtain ⟨p, hp⟩ := ih
      exact ⟨(i, t) :: p, CompletePath.move hi hp⟩

theorem successfulChoice_iff_path
    {s : RunState} {ch : Nat × RunState} :
    SuccessfulChoice s ch ↔
      ∃ rest : List (Nat × RunState), CompletePath s (ch :: rest) := by
  constructor
  · intro h
    rcases h with ⟨hstep, hsol⟩
    obtain ⟨rest, hrest⟩ := solvable_completePath hsol
    exact ⟨rest, CompletePath.move hstep hrest⟩
  · rintro ⟨rest, hpath⟩
    rcases ch with ⟨i, t⟩
    cases hpath with
    | move hstep htail =>
        exact ⟨hstep, completePath_solvable htail⟩

theorem uniqueCompletePath_nil : UniqueCompletePath ([] : RunState) := by
  refine ⟨[], CompletePath.done, ?_⟩
  intro p hp
  cases hp
  rfl

/-- If a nonterminal state has one complete successful path, then its first
edge is a successful first choice. -/
theorem completePath_first_successful
    {s t : RunState} {i : Nat} {rest : List (Nat × RunState)}
    (h : CompletePath s ((i, t) :: rest)) :
    SuccessfulChoice s (i, t) := by
  cases h with
  | move hstep htail =>
      exact ⟨hstep, completePath_solvable htail⟩

/-- The easy half of the target equivalence: a unique complete reduction path
forces a unique successful first move. -/
theorem uniqueCompletePath_uniqueSuccessfulFirst
    {s : RunState}
    (hne : s ≠ [])
    (hu : UniqueCompletePath s) :
    UniqueSuccessfulFirst s := by
  rcases hu with ⟨p, hp, hpuniq⟩
  cases hp with
  | done =>
      exact (hne rfl).elim
  | @move s t i rest hstep htail =>
      refine ⟨(i, t), ⟨hstep, completePath_solvable htail⟩, ?_⟩
      intro ch hch
      obtain ⟨rest', hpath'⟩ := successfulChoice_iff_path.mp hch
      have heq : ch :: rest' = (i, t) :: rest :=
        hpuniq (ch :: rest') hpath'
      exact (List.cons.inj heq).1

/-- Generic induction step for the hard direction.  Same-Game-specific work
is isolated to proving that every successful child of a unique-first state
itself has a unique complete path. -/
theorem uniqueCompletePath_of_uniqueFirst_and_children
    {s : RunState}
    (hne : s ≠ [])
    (hfirst : UniqueSuccessfulFirst s)
    (hchildren :
      ∀ ch : Nat × RunState,
        SuccessfulChoice s ch → UniqueCompletePath ch.2) :
    UniqueCompletePath s := by
  rcases hfirst with ⟨ch0, hch0, hfirstuniq⟩
  rcases hchildren ch0 hch0 with ⟨rest0, hrest0, hrestuniq⟩
  refine ⟨ch0 :: rest0, ?_, ?_⟩
  · rcases hch0 with ⟨hstep0, _⟩
    exact CompletePath.move hstep0 hrest0
  · intro p hp
    cases hp with
    | done =>
        exact (hne rfl).elim
    | @move s t i rest hstep htail =>
        have hch : SuccessfulChoice s (i, t) :=
          ⟨hstep, completePath_solvable htail⟩
        have hchoice : (i, t) = ch0 := hfirstuniq (i, t) hch
        subst ch0
        have hrest : rest = rest0 := hrestuniq rest htail
        subst rest
        rfl

end LC004
