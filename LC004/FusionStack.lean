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
            simp only [fusionLetter,if_pos rfl,Finset.mem_insert,Finset.mem_singleton]
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

#print axioms raw_max_win_iff_fusionEval
#print axioms raw_max_win_iff_fusionReach
end LC004
