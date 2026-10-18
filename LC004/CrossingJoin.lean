import LC004.PartitionCounting
import LC004.GrammarNormalForm

namespace LC004

/-- Two different blocks interleave in the order on positions. -/
def Crossing {n : Nat} (p : Setoid (Fin n)) : Prop :=
  ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧ p a c ∧ p b d ∧ ¬p a b

def leftPairLabels (i : Fin 8) : Nat := [0,1,1,0,2,3,3,2][i.val]!
def nestedPairLabels (i : Fin 8) : Nat := [0,1,2,3,3,2,1,0][i.val]!
def crossingLabels (i : Fin 8) : Nat := [0,1,1,0,0,1,1,0][i.val]!

theorem leftPair_grammar : ClickGrammar [0,1,1,0,2,3,3,2] :=
  (ClickGrammar.pair 0 (ClickGrammar.pair 1 ClickGrammar.empty)).append
    (ClickGrammar.pair 2 (ClickGrammar.pair 3 ClickGrammar.empty))

theorem nestedPair_grammar : ClickGrammar [0,1,2,3,3,2,1,0] :=
  ClickGrammar.pair 0 (ClickGrammar.pair 1
    (ClickGrammar.pair 2 (ClickGrammar.pair 3 ClickGrammar.empty)))

theorem leftPair_noncrossing : ¬Crossing (Setoid.ker leftPairLabels) := by
  simp only [Crossing, Setoid.ker_def]
  decide

theorem nestedPair_noncrossing : ¬Crossing (Setoid.ker nestedPairLabels) := by
  simp only [Crossing, Setoid.ker_def]
  decide

/-- The intersection of two noncrossing equality events can require a
CROSSING partition. Replacing all-partition join by noncrossing join is unsound. -/
theorem noncrossing_pairings_crossing_join :
    Crossing (Setoid.ker leftPairLabels ⊔ Setoid.ker nestedPairLabels) := by
  have hp : Setoid.ker leftPairLabels ≤ Setoid.ker crossingLabels := by
    change ∀ i j : Fin 8, leftPairLabels i = leftPairLabels j →
      crossingLabels i = crossingLabels j
    decide
  have hr : Setoid.ker nestedPairLabels ≤ Setoid.ker crossingLabels := by
    change ∀ i j : Fin 8, nestedPairLabels i = nestedPairLabels j →
      crossingLabels i = crossingLabels j
    decide
  have hj := sup_le hp hr
  refine ⟨0, 1, 3, 5, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · exact (le_sup_left : Setoid.ker leftPairLabels ≤ _)
      (show Setoid.ker leftPairLabels 0 3 from rfl)
  · apply (Setoid.ker leftPairLabels ⊔ Setoid.ker nestedPairLabels).trans' (y := 2)
    · exact (le_sup_left : Setoid.ker leftPairLabels ≤ _)
        (show Setoid.ker leftPairLabels 1 2 from rfl)
    · exact (le_sup_right : Setoid.ker nestedPairLabels ≤ _)
        (show Setoid.ker nestedPairLabels 2 5 from rfl)
  · intro h
    have hbad : crossingLabels 0 = crossingLabels 1 := hj h
    exact (by decide : crossingLabels 0 ≠ crossingLabels 1) hbad

#print axioms leftPair_noncrossing
#print axioms nestedPair_noncrossing
#print axioms noncrossing_pairings_crossing_join

end LC004
