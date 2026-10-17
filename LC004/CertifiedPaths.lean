import LC004.UniqueCanonical

namespace LC004

/-- All successful indexed paths within a depth bound. Finsets prevent
duplicate derivations from inflating the number of index sequences. -/
def pathSetFuel : Nat → RunState → Finset (List Nat)
  | 0, s => if s = [] then {[]} else ∅
  | n + 1, s =>
      (if s = [] then {[]} else ∅) ∪
      (Finset.range s.length).biUnion (fun i =>
        match stepAt s i with
        | none => ∅
        | some t => (pathSetFuel n t).image (List.cons i))

theorem mem_terminalPathSet (s : RunState) (p : List Nat) :
    p ∈ (if s = [] then ({[]} : Finset (List Nat)) else ∅) ↔
      s = [] ∧ p = [] := by
  by_cases hs : s = [] <;> simp [hs]

theorem mem_extendedPathSet (n : Nat) (s : RunState) (i : Nat) (p : List Nat) :
    p ∈ (match stepAt s i with
      | none => (∅ : Finset (List Nat))
      | some t => (pathSetFuel n t).image (List.cons i)) ↔
    ∃ t, stepAt s i = some t ∧
      ∃ rest ∈ pathSetFuel n t, i :: rest = p := by
  cases h : stepAt s i <;> simp [h]

/-- Complete correctness specification, including the exact depth cutoff. -/
theorem mem_pathSetFuel (n : Nat) (s : RunState) (p : List Nat) :
    p ∈ pathSetFuel n s ↔ SuccessfulPath s p ∧ p.length ≤ n := by
  induction n generalizing s p with
  | zero =>
      rw [pathSetFuel, mem_terminalPathSet]
      constructor
      · rintro ⟨rfl, rfl⟩
        simp [SuccessfulPath, follow]
      · rintro ⟨hp, hlen⟩
        have he : p = [] := List.length_eq_zero_iff.mp (by omega)
        subst p
        exact ⟨successfulPath_nil_iff.mp hp, rfl⟩
  | succ n ih =>
      simp only [pathSetFuel, Finset.mem_union, mem_terminalPathSet,
        Finset.mem_biUnion, Finset.mem_range, mem_extendedPathSet]
      constructor
      · intro h
        rcases h with ⟨rfl, rfl⟩ | ⟨i, hi, t, hs, rest, hr, rfl⟩
        · simp [SuccessfulPath, follow]
        · obtain ⟨hrest, hlen⟩ := (ih t rest).mp hr
          constructor
          · simpa [SuccessfulPath, follow, hs] using hrest
          · simpa using Nat.succ_le_succ hlen
      · rintro ⟨hp, hlen⟩
        cases p with
        | nil => exact Or.inl ⟨successfulPath_nil_iff.mp hp, rfl⟩
        | cons i rest =>
            right
            cases hs : stepAt s i with
            | none => simp [SuccessfulPath, follow, hs] at hp
            | some t =>
                have hrest : SuccessfulPath t rest := by
                  simpa [SuccessfulPath, follow, hs] using hp
                have hrestlen : rest.length ≤ n := by
                  simp only [List.length_cons] at hlen
                  omega
                exact ⟨i, indexedStep_index_lt (stepAt_sound hs), t, hs,
                  rest, (ih t rest).mpr ⟨hrest, hrestlen⟩, rfl⟩

theorem pathIndices_length (p : List (Nat × RunState)) :
    (pathIndices p).length = p.length := by
  induction p with
  | nil => rfl
  | cons ch rest ih => simp [pathIndices, ih]

theorem successfulPath_length_le_runs
    {s : RunState} {moves : List Nat} (hp : SuccessfulPath s moves) :
    moves.length ≤ s.length := by
  obtain ⟨p, hcomplete, hindices⟩ := successfulPath_has_completePath hp
  rw [← hindices, pathIndices_length]
  exact completePath_length_le hcomplete

/-- No fuel assumption remains: every successful path is covered. -/
def solutionPaths (s : RunState) : Finset (List Nat) :=
  pathSetFuel s.length s

theorem mem_solutionPaths_iff (s : RunState) (p : List Nat) :
    p ∈ solutionPaths s ↔ SuccessfulPath s p := by
  rw [solutionPaths, mem_pathSetFuel]
  exact ⟨And.left, fun hp => ⟨hp, successfulPath_length_le_runs hp⟩⟩

/-- A computed singleton set is a kernel-checkable uniqueness certificate. -/
theorem uniqueSuccessfulPath_iff_card_solutionPaths (s : RunState) :
    UniqueSuccessfulPath s ↔ (solutionPaths s).card = 1 := by
  constructor
  · rintro ⟨p, hp, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext q
    rw [mem_solutionPaths_iff, Finset.mem_singleton]
    exact ⟨fun hq => huniq q hq, fun he => he ▸ hp⟩
  · intro hcard
    obtain ⟨p, he⟩ := Finset.card_eq_one.mp hcard
    have hp : SuccessfulPath s p := (mem_solutionPaths_iff s p).mp (by rw [he]; simp)
    refine ⟨p, hp, ?_⟩
    intro q hq
    have hmem := (mem_solutionPaths_iff s q).mpr hq
    rw [he] at hmem
    exact Finset.mem_singleton.mp hmem

#print axioms mem_pathSetFuel
#print axioms mem_solutionPaths_iff
#print axioms uniqueSuccessfulPath_iff_card_solutionPaths

end LC004
