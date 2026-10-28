import LC004.EndpointMatchingDyck

namespace LC004

/-- Construct a matching by the first-return decomposition of a Dyck
word. Concatenation and outer enclosure mirror its recursive grammar. -/
theorem dyck_has_endpoint_matching (w : DyckWord) :
    ∃ n, ∃ m : EndpointMatching n, m.toDyck = w := by
  have aux (k : Nat) : ∀ w : DyckWord, w.semilength = k →
      ∃ n, ∃ m : EndpointMatching n, m.toDyck = w := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw
      by_cases hz : w = 0
      · subst w
        exact ⟨0, EndpointMatching.empty, EndpointMatching.toDyck_empty⟩
      · have hin := DyckWord.semilength_insidePart_lt hz
        have hout := DyckWord.semilength_outsidePart_lt hz
        obtain ⟨n, m, hm⟩ := ih w.insidePart.semilength (by omega) w.insidePart rfl
        obtain ⟨j, t, ht⟩ := ih w.outsidePart.semilength (by omega) w.outsidePart rfl
        refine ⟨n + 2 + j, m.nest.append t, ?_⟩
        rw [EndpointMatching.toDyck_append, EndpointMatching.toDyck_nest, hm, ht]
        exact DyckWord.nest_insidePart_add_outsidePart hz
  exact aux w.semilength w rfl

theorem matchingDyckMap_surjective (m : Nat) : Function.Surjective (matchingDyckMap m) := by
  intro w
  obtain ⟨n, e, he⟩ := dyck_has_endpoint_matching w.val
  have hlen : e.toDyck.toList.length = n := matchingToDyckWord_length e.pattern e.pattern_noncrossing
  have hwlen := w.val.two_mul_semilength_eq_length
  rw [w.property] at hwlen
  have heq := congrArg (fun v : DyckWord => v.toList.length) he
  have hn : n = 2 * m := by omega
  subst n
  exact ⟨⟨e.pattern, e.pattern_noncrossing⟩, Subtype.ext he⟩

/-- The actual finite noncrossing matching space has the Catalan count. -/
theorem noncrossing_pair_pattern_count_eq_catalan (m : Nat) :
    noncrossingPairPatternCount (2 * m) = catalan m := by
  classical
  have e := Equiv.ofBijective (matchingDyckMap m)
    ⟨matchingDyckMap_injective m, matchingDyckMap_surjective m⟩
  have h := Fintype.card_congr e
  rw [DyckWord.card_dyckWord_semilength_eq_catalan] at h
  exact h

theorem second_diagonal_matching_count (k : Nat) :
    noncrossingPairPatternCount (2 * k + 2) = catalan (k + 1) := by
  have h := noncrossing_pair_pattern_count_eq_catalan (k + 1)
  simpa only [Nat.mul_add, Nat.mul_one] using h

#print axioms matchingDyckMap_surjective
#print axioms noncrossing_pair_pattern_count_eq_catalan

end LC004
