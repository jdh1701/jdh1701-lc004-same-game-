import LC004.RawCertificateEquivalence

namespace LC004

/-- A stack is stored with its top first. Equal incoming colors may pop or
stay; a different incoming color is pushed. This counts no deletion histories. -/
inductive FusionEval {q : Nat} : List (Fin q) → List (Fin q) → List (Fin q) → Prop where
  | done (s) : FusionEval s [] s
  | push {s w t} (a : Fin q) (h : s.head? ≠ some a) :
      FusionEval (a :: s) w t → FusionEval s (a :: w) t
  | pop {s w t} (a : Fin q) :
      FusionEval s w t → FusionEval (a :: s) (a :: w) t
  | stay {s w t} (a : Fin q) :
      FusionEval (a :: s) w t → FusionEval (a :: s) (a :: w) t

theorem fusionEval_append {q : Nat} {s u m v t : List (Fin q)}
    (h : FusionEval s u m) (k : FusionEval m v t) : FusionEval s (u ++ v) t := by
  induction h with
  | done _ => exact k
  | push a hn _ ih => exact FusionEval.push a hn (ih k)
  | pop a _ ih => exact FusionEval.pop a (ih k)
  | stay a _ ih => exact FusionEval.stay a (ih k)

theorem fusionEval_split {q : Nat} {s u v t : List (Fin q)}
    (h : FusionEval s (u ++ v) t) :
    ∃ m, FusionEval s u m ∧ FusionEval m v t := by
  induction u generalizing s with
  | nil => exact ⟨s,FusionEval.done s,h⟩
  | cons a u ih =>
      cases h with
      | push _ hn hr =>
          obtain ⟨m,hm,ht⟩ := ih hr
          exact ⟨m,FusionEval.push a hn hm,ht⟩
      | pop _ hr =>
          obtain ⟨m,hm,ht⟩ := ih hr
          exact ⟨m,FusionEval.pop a hm,ht⟩
      | stay _ hr =>
          obtain ⟨m,hm,ht⟩ := ih hr
          exact ⟨m,FusionEval.stay a hm,ht⟩

theorem fusionEval_pair_loop {q : Nat} (s : List (Fin q)) (a : Fin q) :
    FusionEval s [a,a] s := by
  by_cases h : s.head? = some a
  · obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp h
    exact FusionEval.stay a (FusionEval.stay a (FusionEval.done _))
  · exact FusionEval.push a h (FusionEval.pop a (FusionEval.done _))

theorem fusionEval_triple_loop {q : Nat} (s : List (Fin q)) (a : Fin q) :
    FusionEval s [a,a,a] s := by
  by_cases h : s.head? = some a
  · obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp h
    exact FusionEval.stay a (FusionEval.stay a (FusionEval.stay a (FusionEval.done _)))
  · exact FusionEval.push a h (FusionEval.stay a (FusionEval.pop a (FusionEval.done _)))

theorem smallErase_lifts_fusionEval {q : Nat} {u v : List (Fin q)}
    (h : SmallErase u v) {s t : List (Fin q)} (k : FusionEval s v t) :
    FusionEval s u t := by
  cases h with
  | pair left right a =>
      obtain ⟨m,hm,ht⟩ := fusionEval_split k
      exact fusionEval_append (fusionEval_append hm (fusionEval_pair_loop m a)) ht
  | triple left right a =>
      obtain ⟨m,hm,ht⟩ := fusionEval_split k
      exact fusionEval_append (fusionEval_append hm (fusionEval_triple_loop m a)) ht

theorem erases_lifts_fusionEval {q : Nat} {u v : List (Fin q)}
    (h : Erases u v) {s t : List (Fin q)} (k : FusionEval s v t) :
    FusionEval s u t := by
  induction h with
  | refl _ => exact k
  | next step rest ih => exact smallErase_lifts_fusionEval step (ih k)

/-- Every accepting stack computation lifts to actual maximal-run winning.
The stay case uses the already proved run-inflation theorem, not a legal
singleton deletion or an assumed grammar equivalence. -/
theorem fusionEval_lifts_raw_win {q : Nat} {s w t : List (Fin q)}
    (h : FusionEval s w t) (ht : RawMaxErases t.reverse []) :
    RawMaxErases (s.reverse ++ w) [] := by
  induction h with
  | done _ => simpa using ht
  | push a hn hr ih =>
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih ht
  | @pop s w t a hr ih =>
      have hh := monochromatic_insertion_preserves_raw_win s.reverse w a 2 (by omega) (ih ht)
      simpa [List.reverse_cons,List.append_assoc,List.replicate_succ] using hh
  | @stay s w t a hr ih =>
      have hw : RawMaxErases (s.reverse ++ a :: w) [] := by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih ht
      have hh := raw_win_inflation hw (raw_inflates_context_cell s.reverse w a 1)
      simpa [List.reverse_cons,List.append_assoc,List.replicate_succ] using hh

theorem raw_max_win_iff_fusionEval {q : Nat} (w : List (Fin q)) :
    RawMaxErases w [] ↔ FusionEval [] w [] := by
  constructor
  · intro h
    exact erases_lifts_fusionEval ((raw_max_win_iff_aux_erases w).mp h) (FusionEval.done [])
  · intro h
    simpa using fusionEval_lifts_raw_win h (RawMaxErases.refl [])

def fusionLetter {q : Nat} (a : Fin q) (s : List (Fin q)) : Finset (List (Fin q)) :=
  match s with
  | [] => {[a]}
  | b :: tail => if b = a then {b :: tail,tail} else {a :: b :: tail}

def fusionReach {q : Nat} (s : List (Fin q)) : List (Fin q) → Finset (List (Fin q))
  | [] => {s}
  | a :: w => (fusionLetter a s).biUnion (fun t => fusionReach t w)

theorem mem_fusionReach_iff {q : Nat} (s w t : List (Fin q)) :
    t ∈ fusionReach s w ↔ FusionEval s w t := by
  induction w generalizing s with
  | nil =>
      simp only [fusionReach,Finset.mem_singleton]
      constructor
      · rintro rfl; exact FusionEval.done _
      · intro h; cases h; rfl
  | cons a w ih =>
      simp only [fusionReach,Finset.mem_biUnion,ih]
      cases s with
      | nil =>
          simp only [fusionLetter,Finset.mem_singleton,exists_eq_left]
          constructor
          · exact FusionEval.push a (by simp)
          · intro h; cases h with | push _ _ hr => exact hr
      | cons b s =>
          by_cases hba : b = a
          · subst b
            rw [show fusionLetter a (a :: s) = {a :: s,s} by simp [fusionLetter]]
            simp only [Finset.mem_insert,Finset.mem_singleton]
            constructor
            · rintro ⟨m,hm,hr⟩
              rcases hm with rfl | rfl
              · exact FusionEval.stay a hr
              · exact FusionEval.pop a hr
            · intro h
              cases h with
              | push _ hn _ => exact (hn (by simp)).elim
              | pop _ hr => exact ⟨s,Or.inr rfl,hr⟩
              | stay _ hr => exact ⟨a::s,Or.inl rfl,hr⟩
          · simp only [fusionLetter,if_neg hba,Finset.mem_singleton,exists_eq_left]
            constructor
            · exact FusionEval.push a (by simpa using hba)
            · intro h
              cases h with
              | push _ _ hr => exact hr
              | pop _ _ => exact (hba rfl).elim
              | stay _ _ => exact (hba rfl).elim

/-- The exact original-game indicator is empty-stack membership in the
Boolean support, for every word length and every finite alphabet. -/
theorem raw_max_win_iff_fusionReach {q : Nat} (w : List (Fin q)) :
    RawMaxErases w [] ↔ [] ∈ fusionReach [] w := by
  rw [raw_max_win_iff_fusionEval,mem_fusionReach_iff]

/-- Adjacent letters differ. This is not pairwise distinctness. -/
def FusionProper {q : Nat} : List (Fin q) → Prop
  | [] => True
  | a :: w => w.head? ≠ some a ∧ FusionProper w

theorem fusionEval_preserves_proper {q : Nat} {s w t : List (Fin q)}
    (h : FusionEval s w t) (hs : FusionProper s) : FusionProper t := by
  induction h with
  | done _ => exact hs
  | push a hn _ ih => exact ih ⟨hn,hs⟩
  | pop a _ ih => exact ih hs.2
  | stay a _ ih => exact ih hs

theorem fusionReach_proper {q : Nat} {w s : List (Fin q)}
    (h : s ∈ fusionReach [] w) : FusionProper s := by
  exact fusionEval_preserves_proper ((mem_fusionReach_iff [] w s).mp h) trivial

/-- Once a proper suffix starts with a different color, it can never empty
an already nonempty stack. -/
theorem fusionEval_proper_blocked {q : Nat} (a : Fin q) (s w : List (Fin q))
    (hw : FusionProper w) (hn : w.head? ≠ some a) :
    ¬ FusionEval (a :: s) w [] := by
  induction w generalizing a s with
  | nil => intro h; cases h
  | cons b w ih =>
      intro h
      cases h with
      | push _ _ hr => exact ih b (a :: s) hw.2 hw.1 hr
      | pop _ _ => exact hn rfl
      | stay _ _ => exact hn rfl

theorem fusionEval_pop_all {q : Nat} (s : List (Fin q)) : FusionEval s s [] := by
  induction s with
  | nil => exact FusionEval.done []
  | cons a s ih => exact FusionEval.pop a ih

/-- A proper suffix accepts exactly its own top-first stack. -/
theorem fusionEval_proper_accept_iff {q : Nat} (s w : List (Fin q))
    (hw : FusionProper w) : FusionEval s w [] ↔ s = w := by
  constructor
  · intro h
    induction w generalizing s with
    | nil => cases h; rfl
    | cons a w ih =>
        cases h with
        | push _ _ hr => exact (fusionEval_proper_blocked a _ w hw.2 hw.1 hr).elim
        | pop _ hr => exact congrArg (List.cons a) (ih _ hw.2 hr)
        | stay _ hr => exact (fusionEval_proper_blocked a _ w hw.2 hw.1 hr).elim
  · rintro rfl
    exact fusionEval_pop_all _

theorem raw_max_win_append_iff_fusion_stack {q : Nat} (u v : List (Fin q)) :
    RawMaxErases (u ++ v) [] ↔
      ∃ s, s ∈ fusionReach [] u ∧ FusionEval s v [] := by
  rw [raw_max_win_iff_fusionEval]
  constructor
  · intro h
    obtain ⟨s,hs,hv⟩ := fusionEval_split h
    exact ⟨s,(mem_fusionReach_iff [] u s).mpr hs,hv⟩
  · rintro ⟨s,hs,hv⟩
    exact fusionEval_append ((mem_fusionReach_iff [] u s).mp hs) hv

theorem raw_max_win_append_proper_iff {q : Nat} (u v : List (Fin q))
    (hv : FusionProper v) :
    RawMaxErases (u ++ v) [] ↔ v ∈ fusionReach [] u := by
  rw [raw_max_win_append_iff_fusion_stack]
  constructor
  · rintro ⟨s,hs,he⟩
    have h := (fusionEval_proper_accept_iff s v hv).mp he
    simpa only [h] using hs
  · intro h
    exact ⟨v,h,fusionEval_pop_all v⟩

/-- Distinct Boolean supports are exactly distinct residual winning languages.
This rules out merging supports while preserving every future word, not an
aggregate counting formula that avoids enumerating them. -/
theorem fusionReach_eq_iff_winning_continuations {q : Nat} (u v : List (Fin q)) :
    fusionReach [] u = fusionReach [] v ↔
      ∀ w, RawMaxErases (u ++ w) [] ↔ RawMaxErases (v ++ w) [] := by
  constructor
  · intro h w
    simp only [raw_max_win_append_iff_fusion_stack,h]
  · intro h
    apply Finset.ext
    intro s
    constructor
    · intro hs
      have hp := fusionReach_proper hs
      exact (raw_max_win_append_proper_iff v s hp).mp
        ((h s).mp ((raw_max_win_append_proper_iff u s hp).mpr hs))
    · intro hs
      have hp := fusionReach_proper hs
      exact (raw_max_win_append_proper_iff u s hp).mp
        ((h s).mpr ((raw_max_win_append_proper_iff v s hp).mpr hs))

#print axioms raw_max_win_iff_fusionEval
#print axioms raw_max_win_iff_fusionReach
#print axioms fusionReach_eq_iff_winning_continuations
end LC004
