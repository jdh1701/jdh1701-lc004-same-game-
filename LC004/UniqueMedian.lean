import LC004.UnconditionalFinal

namespace LC004

/-- In a unique-first bridge state, every successful child move deletes the
newly merged run. This exposes the index conclusion of bridge exchange. -/
theorem unique_bridge_child_index
    {pre post : RunState} {c d : Nat} {bp bq : Bool}
    (hn : Normalized (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post))
    (hu : UniqueSuccessfulChoice
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post))
    (hmain : SuccessfulChoice
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
      (pre.length + 1, pre ++ (c,true) :: post))
    {child : Nat × RunState}
    (hc : SuccessfulChoice (pre ++ (c,true) :: post) child) :
    child.1 = pre.length := by
  by_contra hne
  have hlift := normalizedBridgeExchange_of_structural
    normalizedBridgeStructuralExchange_proved hn
  obtain ⟨alt, halt, hnealt⟩ := hlift child hc hne
  exact uniqueSuccessfulChoice_no_alt hu hmain halt hnealt

/-- Every successful first choice of a normalized nonempty unique-first
state is the median of an odd number of runs. No bound on colours. -/
theorem unique_successful_choice_is_median
    {s : RunState} (hn : Normalized s) (hne : s ≠ [])
    (hu : UniqueSuccessfulChoice s)
    {chosen : Nat × RunState} (hc : SuccessfulChoice s chosen) :
    s.length = 2 * chosen.1 + 1 := by
  have main : ∀ n : Nat, ∀ x : RunState, x.length = n →
      Normalized x → x ≠ [] → UniqueSuccessfulChoice x →
      ∀ ch, SuccessfulChoice x ch → x.length = 2 * ch.1 + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hn' hne' hu' ch hch
      by_cases hone : x.length = 1
      · have hidx := indexedStep_index_lt hch.1
        have hi : ch.1 = 0 := by omega
        omega
      · have hgt : 1 < x.length := by
          have hpos : 0 < x.length := List.length_pos_iff.mpr hne'
          omega
        have hb : BridgeChoice x ch := by
          rcases successfulChoice_classify hch with hno | hb
          · have hlift := normalizedNoMergeExchange_of_structural
              noMergeStructuralExchange_proved hn' hno hch
            exact (uniqueChoice_forbids_full_child_exchange hu' hch
              (noMergeChoice_child_nonempty hgt hno) hlift).elim
          · exact hb
        rcases hb with ⟨pre, post, c, d, bp, bq, rfl, rfl⟩
        have hnorm : Normalized (pre ++ (c,true) :: post) :=
          indexedStep_normalized hn' hch.1
        have hchildne : pre ++ (c,true) :: post ≠ [] := by simp
        have hlift := normalizedBridgeExchange_of_structural
          normalizedBridgeStructuralExchange_proved hn'
        have hchildunique := bridge_child_unique_of_exchange hch hu' hlift
        obtain ⟨child, hchild⟩ :=
          runSolvable_nonempty_has_successfulChoice hchildne hch.2
        have hchildidx : child.1 = pre.length :=
          unique_bridge_child_index hn' hu' hch hchild
        have hlt : (pre ++ (c,true) :: post).length < n := by
          have := indexedStep_length_lt hch.1
          simpa [hx] using this
        have hm := ih _ hlt _ rfl hnorm hchildne hchildunique child hchild
        simp only [List.length_append, List.length_cons] at hm ⊢
        omega
  exact main s.length s rfl hn hne hu chosen hc

theorem unique_successful_first_is_median
    {s : RunState} (hn : Normalized s) (hne : s ≠ [])
    (hu : UniqueSuccessfulFirst s) {i : Nat} (hi : SuccessfulMove s i) :
    s.length = 2 * i + 1 := by
  obtain ⟨t, ht⟩ := successfulMove_iff_exists_successfulChoice.mp hi
  exact unique_successful_choice_is_median hn hne
    (uniqueSuccessfulFirst_iff_uniqueSuccessfulChoice.mp hu) ht

theorem unique_successful_path_odd_runs
    {s : RunState} (hn : Normalized s) (hne : s ≠ [])
    (hu : UniqueSuccessfulPath s) : Odd s.length := by
  have hf := (unconditional_executable_unique_first_iff_path hn hne).mpr hu
  obtain ⟨i, hi, _⟩ := hf
  have hm := unique_successful_first_is_median hn hne
    ((unconditional_executable_unique_first_iff_path hn hne).mpr hu) hi
  exact ⟨i, by omega⟩

/-- Necessary colour-skeleton symmetry for a unique successful path. The
Boolean flags, and the original raw run lengths, need not be palindromic. -/
theorem unique_successful_choice_color_palindrome
    {s : RunState} (hn : Normalized s) (hne : s ≠ [])
    (hu : UniqueSuccessfulChoice s) :
    (s.map Prod.fst).reverse = s.map Prod.fst := by
  have main : ∀ n : Nat, ∀ x : RunState, x.length = n →
      Normalized x → x ≠ [] → UniqueSuccessfulChoice x →
      (x.map Prod.fst).reverse = x.map Prod.fst := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hn' hne' hu'
      by_cases hone : x.length = 1
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hone
        rfl
      · obtain ⟨ch, hch⟩ := hu'.exists
        have hgt : 1 < x.length := by
          have hpos : 0 < x.length := List.length_pos_iff.mpr hne'
          omega
        have hb : BridgeChoice x ch := by
          rcases successfulChoice_classify hch with hno | hb
          · have hlift := normalizedNoMergeExchange_of_structural
              noMergeStructuralExchange_proved hn' hno hch
            exact (uniqueChoice_forbids_full_child_exchange hu' hch
              (noMergeChoice_child_nonempty hgt hno) hlift).elim
          · exact hb
        rcases hb with ⟨pre, post, c, d, bp, bq, rfl, rfl⟩
        have hnorm : Normalized (pre ++ (c,true) :: post) :=
          indexedStep_normalized hn' hch.1
        have hchildne : pre ++ (c,true) :: post ≠ [] := by simp
        have hlift := normalizedBridgeExchange_of_structural
          normalizedBridgeStructuralExchange_proved hn'
        have hchildunique := bridge_child_unique_of_exchange hch hu' hlift
        obtain ⟨child, hchild⟩ :=
          runSolvable_nonempty_has_successfulChoice hchildne hch.2
        have hidx : child.1 = pre.length :=
          unique_bridge_child_index hn' hu' hch hchild
        have hm := unique_successful_choice_is_median
          hnorm hchildne hchildunique hchild
        have hbalance : pre.length = post.length := by
          simp only [List.length_append, List.length_cons] at hm
          omega
        have hlt : (pre ++ (c,true) :: post).length < n := by
          have := indexedStep_length_lt hch.1
          simpa [hx] using this
        have hpal := ih _ hlt _ rfl hnorm hchildne hchildunique
        have hrev : (post.map Prod.fst).reverse = pre.map Prod.fst := by
          apply List.append_inj_left (t₁ := [c] ++ (pre.map Prod.fst).reverse)
            (t₂ := c :: post.map Prod.fst)
          · simpa [List.map_append, List.map_cons, List.reverse_append,
              List.reverse_cons, List.append_assoc] using hpal
          · simp [hbalance]
        have hrev' : (pre.map Prod.fst).reverse = post.map Prod.fst := by
          simpa using (congrArg List.reverse hrev).symm
        simp [List.map_append, List.map_cons, List.reverse_append,
          List.reverse_cons, hrev, hrev', List.append_assoc]
  exact main s.length s rfl hn hne hu

theorem unique_successful_path_color_palindrome
    {s : RunState} (hn : Normalized s) (hne : s ≠ [])
    (hu : UniqueSuccessfulPath s) :
    (s.map Prod.fst).reverse = s.map Prod.fst := by
  apply unique_successful_choice_color_palindrome hn hne
  exact uniqueSuccessfulFirst_iff_uniqueSuccessfulChoice.mp
    ((unconditional_executable_unique_first_iff_path hn hne).mpr hu)

#print axioms unique_successful_choice_is_median
#print axioms unique_successful_first_is_median
#print axioms unique_successful_path_odd_runs
#print axioms unique_successful_path_color_palindrome

end LC004
