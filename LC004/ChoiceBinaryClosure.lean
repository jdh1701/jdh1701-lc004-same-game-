import LC004.ChoiceFunctionalElimination

namespace LC004

/-- If `A` is exactly the set of tuples satisfying a family of pairwise binary
constraints `C`, and each pairwise constraint is closed under the majority
operation, then `A` itself is closed under the pointwise majority operation.
This is the bridge Section 4.1 of the paper proof needs: it upgrades
"every pairwise exact projection is closed under majority" (a fact about
projections of `A`) together with the binary spec of `A` to the global
`ChoiceSolutionsClosed A` hypothesis every downstream theorem assumes. -/
theorem choiceSolutionsClosed_of_binary_spec {ι : Type*} {D : ι → Type*}
    [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hCclosed : ∀ i j, i ≠ j → ChoiceRelationClosed (C i j)) :
    ChoiceSolutionsClosed A := by
  intro a ha b hb c hc
  apply (hspec _).mpr
  intro i j hij
  exact hCclosed i j hij (a i) (a j) (b i) (b j) (c i) (c j)
    ((hspec a).mp ha i j hij) ((hspec b).mp hb i j hij) ((hspec c).mp hc i j hij)

/-- Converse direction packaged for convenience: if `A`'s binary spec `C` is
pairwise closed under majority, `A` is simultaneously majority-closed and
binary-determined (the two structural hypotheses `ChoiceSolutionsClosed` and
`ChoiceBinaryDetermined` that the reduced-system theorem needs), from a single
geometric input about the pairwise relations. -/
theorem choiceSolutionsClosed_and_binaryDetermined_of_binary_spec
    {ι : Type*} {D : ι → Type*} [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hCclosed : ∀ i j, i ≠ j → ChoiceRelationClosed (C i j)) :
    ChoiceSolutionsClosed A ∧ ChoiceBinaryDetermined A :=
  ⟨choiceSolutionsClosed_of_binary_spec A C hspec hCclosed,
    choiceBinaryDetermined_of_binary_constraints A C hspec⟩

#print axioms choiceSolutionsClosed_of_binary_spec
#print axioms choiceSolutionsClosed_and_binaryDetermined_of_binary_spec
end LC004
