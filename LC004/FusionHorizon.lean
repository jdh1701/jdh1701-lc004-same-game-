import LC004.FusionStack

namespace LC004

/-- Each input symbol can remove at most one stack symbol. -/
theorem fusionEval_length_bound {q : Nat} {s w t : List (Fin q)}
    (h : FusionEval s w t) : s.length ≤ w.length + t.length := by
  induction h with
  | done _ => simp
  | push a hn hr ih => simp only [List.length_cons] at *; omega
  | pop a hr ih => simp only [List.length_cons] at *; omega
  | stay a hr ih => simp only [List.length_cons] at *; omega

def fusionTrim {q : Nat} (r : Nat) (S : Finset (List (Fin q))) :
    Finset (List (Fin q)) := S.filter (fun s => s.length ≤ r)

def FusionAccepts {q : Nat} (S : Finset (List (Fin q))) (w : List (Fin q)) : Prop :=
  ∃ s ∈ S, FusionEval s w []

/-- Trimming states beyond the remaining input length preserves acceptance. -/
theorem fusionAccepts_trim_iff {q : Nat} (S : Finset (List (Fin q)))
    (w : List (Fin q)) (r : Nat) (hw : w.length ≤ r) :
    FusionAccepts (fusionTrim r S) w ↔ FusionAccepts S w := by
  constructor
  · rintro ⟨s,hs,he⟩
    exact ⟨s,(Finset.mem_filter.mp hs).1,he⟩
  · rintro ⟨s,hs,he⟩
    have hb := fusionEval_length_bound he
    refine ⟨s,Finset.mem_filter.mpr ⟨hs,?_⟩,he⟩
    have hl : s.length ≤ w.length := by simpa using hb
    exact hl.trans hw

theorem fusionAccepts_proper_iff {q : Nat} (S : Finset (List (Fin q)))
    (w : List (Fin q)) (hw : FusionProper w) :
    FusionAccepts S w ↔ w ∈ S := by
  constructor
  · rintro ⟨s,hs,he⟩
    have h := (fusionEval_proper_accept_iff s w hw).mp he
    simpa only [h] using hs
  · intro h
    exact ⟨w,h,fusionEval_pop_all w⟩

/-- A precise finite-horizon minimality theorem: no distinct truncated sets
of proper stacks have the same answers on every suffix of length at most r.
This is not minimality for averaged counts or for suffixes of exactly r. -/
theorem fusionTrim_eq_iff_bounded_continuations {q : Nat}
    (S T : Finset (List (Fin q))) (r : Nat)
    (hS : ∀ s ∈ S, FusionProper s) (hT : ∀ t ∈ T, FusionProper t) :
    fusionTrim r S = fusionTrim r T ↔
      ∀ w, w.length ≤ r → (FusionAccepts S w ↔ FusionAccepts T w) := by
  constructor
  · intro h w hw
    rw [← fusionAccepts_trim_iff S w r hw,← fusionAccepts_trim_iff T w r hw,h]
  · intro h
    apply Finset.ext
    intro s
    simp only [fusionTrim,Finset.mem_filter]
    constructor
    · rintro ⟨hs,hl⟩
      have hp := hS s hs
      exact ⟨(fusionAccepts_proper_iff T s hp).mp
        ((h s hl).mp ((fusionAccepts_proper_iff S s hp).mpr hs)),hl⟩
    · rintro ⟨ht,hl⟩
      have hp := hT s ht
      exact ⟨(fusionAccepts_proper_iff S s hp).mp
        ((h s hl).mpr ((fusionAccepts_proper_iff T s hp).mpr ht)),hl⟩

/-- Every prefix of the actual game is represented by its trimmed support,
exactly for all continuations within the horizon. -/
theorem raw_max_win_append_iff_trimmed_fusion {q : Nat}
    (u w : List (Fin q)) (r : Nat) (hw : w.length ≤ r) :
    RawMaxErases (u ++ w) [] ↔ FusionAccepts (fusionTrim r (fusionReach [] u)) w := by
  rw [fusionAccepts_trim_iff _ w r hw,raw_max_win_append_iff_fusion_stack]
  rfl

#print axioms fusionTrim_eq_iff_bounded_continuations
#print axioms raw_max_win_append_iff_trimmed_fusion
end LC004
