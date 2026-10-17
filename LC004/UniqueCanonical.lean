import LC004.UniqueMedian

namespace LC004

/-- Descending current-run indices: `descendingChoices (m+1) = [m,...,0]`. -/
def descendingChoices : Nat → List Nat
  | 0 => []
  | n + 1 => n :: descendingChoices n

theorem descendingChoices_length (n : Nat) :
    (descendingChoices n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descendingChoices, ih]

/-- The candidate index sequence is determined solely by the initial run
count. Even run counts are included in the definition, not assumed unique. -/
def medianPath (runs : Nat) : List Nat :=
  descendingChoices ((runs + 1) / 2)

/-- The tail of a unique successful relational path is itself unique.
This is a generic path fact and needs no normalization or exchange lemma. -/
theorem uniqueCompletePath_child
    {s t : RunState} {i : Nat} {rest : List (Nat × RunState)}
    (hu : UniqueCompletePath s)
    (hs : IndexedStep s i t) (ht : CompletePath t rest) :
    UniqueCompletePath t := by
  obtain ⟨p, hp, huniq⟩ := hu
  refine ⟨rest, ht, ?_⟩
  intro other hother
  have h1 := huniq ((i,t) :: other) (CompletePath.move hs hother)
  have h2 := huniq ((i,t) :: rest) (CompletePath.move hs ht)
  exact (List.cons.inj (h1.trans h2.symm)).2

/-- A unique successful path has descending indices and exactly half the
odd run count, rounded up, moves. The empty source is retained explicitly. -/
theorem unique_completePath_shape
    {s : RunState} {p : List (Nat × RunState)} (hp : CompletePath s p) :
    Normalized s → UniqueCompletePath s →
    pathIndices p = descendingChoices p.length ∧
      (s = [] ∨ s.length + 1 = 2 * p.length) := by
  induction hp with
  | done =>
      intro hn hu
      exact ⟨rfl, Or.inl rfl⟩
  | @move s t i rest hs ht ih =>
      intro hn hu
      have hne : s ≠ [] := by
        intro he
        subst s
        exact indexedStep_nil_false hs
      have hchoice : UniqueSuccessfulChoice s :=
        uniqueCompletePath_uniqueSuccessfulChoice hne hu
      have hm : s.length = 2 * i + 1 :=
        unique_successful_choice_is_median (chosen := (i,t)) hn hne hchoice
          ⟨hs, completePath_solvable ht⟩
      have hut : UniqueCompletePath t := uniqueCompletePath_child hu hs ht
      obtain ⟨hind, hsize⟩ := ih (indexedStep_normalized hn hs) hut
      have hdelta : t.length + 1 = s.length ∨ t.length + 2 = s.length := by
        cases hs with
        | noMerge =>
            left
            simp only [List.length_append, List.length_cons]
            omega
        | merge =>
            right
            simp only [List.length_append, List.length_cons]
            omega
      have hi : i = rest.length := by
        rcases hdelta with hdelta | hdelta
        · rcases hsize with he | hsize
          · have hbound := completePath_length_le ht
            simp only [he, List.length_nil] at hbound hdelta
            omega
          · omega
        · rcases hsize with he | hsize
          · simp only [he, List.length_nil] at hdelta
            omega
          · omega
      constructor
      · simpa [pathIndices, descendingChoices, hi] using
          congrArg (fun xs : List Nat => rest.length :: xs) hind
      · right
        simp only [List.length_cons]
        omega

/-- Universal index formula for the sole complete solution, independent of
palette size and run weights, under the existing normalized game semantics. -/
theorem unique_successful_path_eq_medianPath
    {s : RunState} {moves : List Nat}
    (hn : Normalized s) (hu : UniqueSuccessfulPath s)
    (hp : SuccessfulPath s moves) :
    moves = medianPath s.length := by
  obtain ⟨p, hcomplete, hindices⟩ := successfulPath_has_completePath hp
  have huc := uniqueSuccessfulPath_iff_uniqueCompletePath.mp hu
  obtain ⟨hind, hsize⟩ := unique_completePath_shape hcomplete hn huc
  have hlength : p.length = (s.length + 1) / 2 := by
    rcases hsize with he | hsize
    · have hbound := completePath_length_le hcomplete
      simp only [he, List.length_nil] at hbound ⊢
      omega
    · omega
  calc
    moves = pathIndices p := hindices.symm
    _ = descendingChoices p.length := hind
    _ = medianPath s.length := by rw [hlength]; rfl

theorem unique_successful_path_length
    {s : RunState} {moves : List Nat}
    (hn : Normalized s) (hu : UniqueSuccessfulPath s)
    (hp : SuccessfulPath s moves) :
    moves.length = (s.length + 1) / 2 := by
  rw [unique_successful_path_eq_medianPath hn hu hp]
  exact descendingChoices_length _

/-- The fixed candidate is an actual successful path whenever uniqueness
holds. Success of the candidate alone is deliberately not a converse. -/
theorem unique_successful_path_medianPath_success
    {s : RunState} (hn : Normalized s) (hu : UniqueSuccessfulPath s) :
    SuccessfulPath s (medianPath s.length) := by
  have huniq := hu
  obtain ⟨moves, hp, _⟩ := hu
  have heq := unique_successful_path_eq_medianPath hn huniq hp
  simpa [heq] using hp

/-- If the fixed centre-outward candidate fails, no unique successful path
exists. This is a rejection certificate, not a complete solvability test. -/
theorem medianPath_failure_excludes_unique
    {s : RunState} (hn : Normalized s)
    (hf : ¬ SuccessfulPath s (medianPath s.length)) :
    ¬ UniqueSuccessfulPath s := by
  intro hu
  exact hf (unique_successful_path_medianPath_success hn hu)

#print axioms unique_successful_path_eq_medianPath
#print axioms unique_successful_path_length
#print axioms unique_successful_path_medianPath_success

end LC004
