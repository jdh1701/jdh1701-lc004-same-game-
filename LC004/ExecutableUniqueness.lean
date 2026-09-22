import LC004.ExecutableCorrespondence
import LC004.IndexedDeterminism
import LC004.SuccessfulPaths

namespace LC004

theorem successfulMove_iff_exists_successfulChoice
    {s : RunState} {i : Nat} :
    SuccessfulMove s i ↔
      ∃ t : RunState, SuccessfulChoice s (i, t) := by
  constructor
  · rintro ⟨t, hstep, hsol⟩
    exact ⟨t, stepAt_sound hstep, hsol⟩
  · rintro ⟨t, hstep, hsol⟩
    exact ⟨t, stepAt_complete hstep, hsol⟩

/-- The executable notion of a unique successful run index is equivalent to
the relational notion of a unique successful indexed choice. -/
theorem uniqueSuccessfulFirst_iff_uniqueSuccessfulChoice
    {s : RunState} :
    UniqueSuccessfulFirst s ↔ UniqueSuccessfulChoice s := by
  constructor
  · rintro ⟨i, hi, hiuniq⟩
    obtain ⟨t, hchoice⟩ :=
      successfulMove_iff_exists_successfulChoice.mp hi
    refine ⟨(i, t), hchoice, ?_⟩
    intro ch hch
    have hm : SuccessfulMove s ch.1 :=
      successfulMove_iff_exists_successfulChoice.mpr ⟨ch.2, hch⟩
    have hidx : ch.1 = i := hiuniq ch.1 hm
    exact successfulChoice_eq_of_index_eq hch hchoice hidx
  · rintro ⟨ch, hch, huniq⟩
    have hm : SuccessfulMove s ch.1 :=
      successfulMove_iff_exists_successfulChoice.mpr ⟨ch.2, hch⟩
    refine ⟨ch.1, hm, ?_⟩
    intro i hi
    obtain ⟨t, hit⟩ :=
      successfulMove_iff_exists_successfulChoice.mp hi
    have heq : (i, t) = ch := huniq (i, t) hit
    exact congrArg Prod.fst heq

def pathIndices : List (Nat × RunState) → List Nat
  | [] => []
  | ch :: rest => ch.1 :: pathIndices rest

theorem completePath_follow
    {s : RunState} {p : List (Nat × RunState)}
    (h : CompletePath s p) :
    follow s (pathIndices p) = some [] := by
  induction h with
  | done =>
      rfl
  | move hstep htail ih =>
      simp only [pathIndices, follow]
      rw [stepAt_complete hstep]
      exact ih

theorem successfulPath_has_completePath
    {s : RunState} {moves : List Nat}
    (h : SuccessfulPath s moves) :
    ∃ p : List (Nat × RunState),
      CompletePath s p ∧ pathIndices p = moves := by
  induction moves generalizing s with
  | nil =>
      simp only [SuccessfulPath, follow] at h
      have hs : s = [] := Option.some.inj h
      subst s
      exact ⟨[], CompletePath.done, rfl⟩
  | cons i rest ih =>
      simp only [SuccessfulPath, follow] at h
      cases hstep : stepAt s i with
      | none =>
          simp [hstep] at h
      | some t =>
          have htail : SuccessfulPath t rest := by
            simpa [SuccessfulPath, hstep] using h
          obtain ⟨p, hp, hidx⟩ := ih htail
          exact ⟨(i, t) :: p, CompletePath.move (stepAt_sound hstep) hp,
            by simp [pathIndices, hidx]⟩

theorem completePath_eq_of_same_indices
    {s : RunState} {p q : List (Nat × RunState)}
    (hp : CompletePath s p)
    (hq : CompletePath s q)
    (hidx : pathIndices p = pathIndices q) :
    p = q := by
  induction hp generalizing q with
  | done =>
      have hqnil : q = [] := by
        have hlen := completePath_length_le hq
        have hz : q.length = 0 := by
          simpa using hlen
        exact List.length_eq_zero.mp hz
      subst q
      rfl
  | @move s t i rest hstep htail ih =>
      cases q with
      | nil =>
          simp [pathIndices] at hidx
      | cons ch qrest =>
          rcases ch with ⟨j, u⟩
          rcases completePath_cons_iff.mp hq with ⟨hstep2, htail2⟩
          simp only [pathIndices, List.cons.injEq] at hidx
          have hij : i = j := hidx.1
          subst j
          have htu : t = u := indexedStep_target_unique hstep hstep2
          subst u
          have hrest : rest = qrest := ih htail2 hidx.2
          subst qrest
          rfl

/-- Complete relational paths and executable index paths have the same
uniqueness content. -/
theorem uniqueSuccessfulPath_iff_uniqueCompletePath
    {s : RunState} :
    UniqueSuccessfulPath s ↔ UniqueCompletePath s := by
  constructor
  · rintro ⟨moves, hmoves, hmuniq⟩
    obtain ⟨p, hp, hpidx⟩ := successfulPath_has_completePath hmoves
    refine ⟨p, hp, ?_⟩
    intro q hq
    have hqsuccess : SuccessfulPath s (pathIndices q) :=
      completePath_follow hq
    have hindices : pathIndices q = moves :=
      hmuniq (pathIndices q) hqsuccess
    have hsame : pathIndices q = pathIndices p := by
      exact hindices.trans hpidx.symm
    exact completePath_eq_of_same_indices hq hp hsame
  · rintro ⟨p, hp, hpuniq⟩
    have hmoves : SuccessfulPath s (pathIndices p) :=
      completePath_follow hp
    refine ⟨pathIndices p, hmoves, ?_⟩
    intro moves hm
    obtain ⟨q, hq, hqidx⟩ := successfulPath_has_completePath hm
    have heq : q = p := hpuniq q hq
    subst q
    exact hqidx.symm

end LC004
