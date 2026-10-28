import LC004.PairFamilyInsertion
import LC004.NoncrossingBlockFamily
import LC004.FourBlockOverlapCorollary

namespace LC004

theorem pairFamily_cons_iff (e : Nat × Nat) (edges : List (Nat × Nat)) :
    PairFamilyNoncrossing (e :: edges) ↔
      PairFamilyNoncrossing edges ∧
      ∀ f ∈ edges, ¬ PairCross f.1 f.2 e.1 e.2 := by
  constructor
  · intro h
    exact ⟨fun a ha b hb => h a (by simp [ha]) b (by simp [hb]),
      fun f hf => h f (by simp [hf]) e (by simp)⟩
  · rintro ⟨h, he⟩ a ha b hb
    rcases List.mem_cons.mp ha with haEq | ha
    · subst a
      rcases List.mem_cons.mp hb with hbEq | hb
      · subst b
        unfold PairCross
        omega
      · exact (pairCross_symmetric e.1 e.2 b.1 b.2).not.mpr (he b hb)
    · rcases List.mem_cons.mp hb with hbEq | hb
      · subst b
        exact he a ha
      · exact h a ha b hb

inductive FourRefinement where
  | separated
  | nested
  | interleaved
  deriving DecidableEq, Fintype

def fourRefinementEdges (a b c d : Nat) : FourRefinement → List (Nat × Nat)
  | .separated => [(a,b), (c,d)]
  | .nested => [(a,d), (b,c)]
  | .interleaved => [(a,c), (b,d)]

def FourRefinementValid (edges : List (Nat × Nat)) (a b c d : Nat)
    (r : FourRefinement) : Prop :=
  PairFamilyNoncrossing (fourRefinementEdges a b c d r ++ edges)

theorem separated_refinement_iff (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    FourRefinementValid edges a b c d .separated ↔
      PairFamilyNoncrossing edges ∧
      ∀ e ∈ edges, ¬ PairCross e.1 e.2 a b ∧ ¬ PairCross e.1 e.2 c d := by
  change PairFamilyNoncrossing ((a,b) :: (c,d) :: edges) ↔ _
  rw [pairFamily_cons_iff, pairFamily_cons_iff]
  simp only [List.forall_mem_cons]
  have hno : ¬ PairCross c d a b := by unfold PairCross; omega
  constructor
  · rintro ⟨⟨hp, hsecond⟩, _, hfirst⟩
    exact ⟨hp, fun e he => ⟨hfirst e he, hsecond e he⟩⟩
  · rintro ⟨hp, hext⟩
    exact ⟨⟨hp, fun e he => (hext e he).2⟩, hno, fun e he => (hext e he).1⟩

theorem nested_refinement_iff (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    FourRefinementValid edges a b c d .nested ↔
      PairFamilyNoncrossing edges ∧
      ∀ e ∈ edges, ¬ PairCross e.1 e.2 a d ∧ ¬ PairCross e.1 e.2 b c := by
  change PairFamilyNoncrossing ((a,d) :: (b,c) :: edges) ↔ _
  rw [pairFamily_cons_iff, pairFamily_cons_iff]
  simp only [List.forall_mem_cons]
  have hno : ¬ PairCross b c a d := by unfold PairCross; omega
  constructor
  · rintro ⟨⟨hp, hsecond⟩, _, hfirst⟩
    exact ⟨hp, fun e he => ⟨hfirst e he, hsecond e he⟩⟩
  · rintro ⟨hp, hext⟩
    exact ⟨⟨hp, fun e he => (hext e he).2⟩, hno, fun e he => (hext e he).1⟩

theorem interleaved_refinement_invalid (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ¬ FourRefinementValid edges a b c d .interleaved := by
  intro h
  exact h (a,c) (by simp [fourRefinementEdges])
    (b,d) (by simp [fourRefinementEdges]) (Or.inl ⟨hab, hbc, hcd⟩)

/-- The local four-block overlap criterion holds simultaneously for
an arbitrary family of forced pairs, including their mutual crossings. -/
theorem both_refinements_valid_iff (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hordered : ∀ e ∈ edges, e.1 < e.2)
    (hdisjoint : ∀ e ∈ edges,
      (e.1 ≠ a ∧ e.1 ≠ b ∧ e.1 ≠ c ∧ e.1 ≠ d) ∧
      (e.2 ≠ a ∧ e.2 ≠ b ∧ e.2 ≠ c ∧ e.2 ≠ d)) :
    (FourRefinementValid edges a b c d .separated ∧
      FourRefinementValid edges a b c d .nested) ↔
    (PairFamilyNoncrossing edges ∧
      ∀ e ∈ edges, ¬ FourBlockCross e.1 e.2 a b c d) := by
  rw [separated_refinement_iff edges hab hbc hcd,
    nested_refinement_iff edges hab hbc hcd]
  constructor
  · rintro ⟨⟨hp, hs⟩, ⟨_, hn⟩⟩
    refine ⟨hp, ?_⟩
    intro e he
    exact (both_pairings_compatible_iff_block_noncrossing
      (hordered e he) hab hbc hcd (hdisjoint e he).1 (hdisjoint e he).2).mp
      ⟨(hs e he).1, (hs e he).2, (hn e he).1, (hn e he).2⟩
  · rintro ⟨hp, hblock⟩
    have hext : ∀ e ∈ edges,
        ¬ PairCross e.1 e.2 a b ∧ ¬ PairCross e.1 e.2 c d ∧
        ¬ PairCross e.1 e.2 a d ∧ ¬ PairCross e.1 e.2 b c := by
      intro e he
      exact (both_pairings_compatible_iff_block_noncrossing
        (hordered e he) hab hbc hcd (hdisjoint e he).1 (hdisjoint e he).2).mpr
        (hblock e he)
    exact ⟨⟨hp, fun e he => ⟨(hext e he).1, (hext e he).2.1⟩⟩,
      hp, fun e he => ⟨(hext e he).2.2.1, (hext e he).2.2.2⟩⟩

noncomputable def validFourRefinements (edges : List (Nat × Nat))
    (a b c d : Nat) : Finset FourRefinement := by
  classical
  exact Finset.univ.filter (FourRefinementValid edges a b c d)

noncomputable def refinementIndicator (P : Prop) : Nat := by
  classical
  exact if P then 1 else 0

theorem valid_four_refinements_card (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (validFourRefinements edges a b c d).card =
      refinementIndicator (FourRefinementValid edges a b c d .separated) +
      refinementIndicator (FourRefinementValid edges a b c d .nested) := by
  classical
  have huniv : (Finset.univ : Finset FourRefinement) =
      {.separated, .nested, .interleaved} := by
    ext r
    cases r <;> simp
  have hbad := interleaved_refinement_invalid edges hab hbc hcd
  by_cases hs : FourRefinementValid edges a b c d .separated <;>
    by_cases hn : FourRefinementValid edges a b c d .nested <;>
    simp [validFourRefinements, refinementIndicator, huniv,
      Finset.filter_insert, hbad, hs, hn]

theorem valid_four_refinements_card_le_two (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (validFourRefinements edges a b c d).card ≤ 2 := by
  classical
  rw [valid_four_refinements_card edges hab hbc hcd]
  unfold refinementIndicator
  split_ifs <;> omega

/-- Exact double-refinement classification for an arbitrary forced
pair family. This supplies the geometric overlap condition, but does
not by itself count the global set of color-isomorphism patterns. -/
theorem valid_four_refinements_card_eq_two_iff (edges : List (Nat × Nat))
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hordered : ∀ e ∈ edges, e.1 < e.2)
    (hdisjoint : ∀ e ∈ edges,
      (e.1 ≠ a ∧ e.1 ≠ b ∧ e.1 ≠ c ∧ e.1 ≠ d) ∧
      (e.2 ≠ a ∧ e.2 ≠ b ∧ e.2 ≠ c ∧ e.2 ≠ d)) :
    (validFourRefinements edges a b c d).card = 2 ↔
      PairFamilyNoncrossing edges ∧
      ∀ e ∈ edges, ¬ FourBlockCross e.1 e.2 a b c d := by
  classical
  rw [← both_refinements_valid_iff edges hab hbc hcd hordered hdisjoint,
    valid_four_refinements_card edges hab hbc hcd]
  by_cases hs : FourRefinementValid edges a b c d .separated <;>
    by_cases hn : FourRefinementValid edges a b c d .nested <;>
    simp [refinementIndicator, hs, hn]

#print axioms both_refinements_valid_iff
#print axioms valid_four_refinements_card_le_two
#print axioms valid_four_refinements_card_eq_two_iff

end LC004
