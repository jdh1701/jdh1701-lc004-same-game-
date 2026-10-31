import LC004.LocalCertificateCatalogues

namespace LC004

/-- Alternation of two disjoint chords in increasing linear coordinates. -/
def inflationGapCross (a b x y : Nat) : Prop :=
  (a < x ∧ x < b ∧ b < y) ∨ (x < a ∧ a < y ∧ y < b)

/-- Five old points; the gap between the first two contains no outside point.
The four remaining gaps are represented by 3,5,7,9. -/
def fiveGapAvoids (s : Fin 5) (g h : Fin 4) : Prop :=
  ∀ u v : Fin 5, localNC5Color s u = localNC5Color s v →
    ¬ inflationGapCross (2*u.val) (2*v.val) (2*g.val+3) (2*h.val+3)

/-- After inflation the first three points are consecutive within their class,
and both intervening gaps are empty. Outside gaps become 5,7,9,11. -/
def sixGapAvoids (s : Fin 8) (g h : Fin 4) : Prop :=
  ∀ u v : Fin 6, localNC6Color s u = localNC6Color s v →
    ¬ inflationGapCross (2*u.val) (2*v.val) (2*g.val+5) (2*h.val+5)

/-- Exact replacement map in the existing Lean catalogue's ordering. -/
def gapInflationMap : Fin 8 → Fin 5 := ![2,4,0,1,0,3,1,4]

/-- All outside chord tests agree with the mapped old certificate. -/
theorem adjacent_inflation_gap_iff : ∀ s : Fin 8, ∀ g h : Fin 4,
    sixGapAvoids s g h ↔ fiveGapAvoids (gapInflationMap s) g h := by
  unfold sixGapAvoids fiveGapAvoids inflationGapCross gapInflationMap
  decide +kernel

/-- The two exceptional old states permit every old state whenever permitted.
They cannot occur in a context with only two globally feasible tuples. -/
theorem five_gap_exceptional_universal : ∀ s : Fin 5, s = 3 ∨ s = 4 →
    ∀ g h : Fin 4, fiveGapAvoids s g h → ∀ t : Fin 5, fiveGapAvoids t g h := by
  unfold fiveGapAvoids inflationGapCross
  decide +kernel

def fiveGapContext {X : Type*} (R : X → Fin 4 → Fin 4 → Prop)
    (x : X) (s : Fin 5) : Prop := ∀ g h, R x g h → fiveGapAvoids s g h

def sixGapContext {X : Type*} (R : X → Fin 4 → Fin 4 → Prop)
    (x : X) (s : Fin 8) : Prop := ∀ g h, R x g h → sixGapAvoids s g h

theorem five_gap_not_two_cover : ∀ s t : Fin 5,
    ¬ (∀ q : Fin 5, q = s ∨ q = t) := by decide +kernel

/-- A complete two-tuple family excludes both universal local states. -/
theorem adjacent_inflation_two_family_regular {X : Type*}
    (C : X → Prop) (R : X → Fin 4 → Fin 4 → Prop)
    (a b : X) (s t : Fin 5)
    (H : ∀ x q, C x ∧ fiveGapContext R x q ↔
      (x = a ∧ q = s) ∨ (x = b ∧ q = t)) :
    ∀ x q, C x ∧ fiveGapContext R x q → q ≠ 3 ∧ q ≠ 4 := by
  intro x q hx
  have hn : ¬ (q = 3 ∨ q = 4) := by
    intro hq
    apply five_gap_not_two_cover s t
    intro r
    have hr : fiveGapContext R x r := by
      intro g h hR
      exact five_gap_exceptional_universal q hq g h (hx.2 g h hR) r
    rcases (H x r).mp ⟨hx.1,hr⟩ with ⟨_,hs⟩ | ⟨_,ht⟩
    · exact Or.inl hs
    · exact Or.inr ht
  exact ⟨fun h => hn (Or.inl h),fun h => hn (Or.inr h)⟩

/-- Arbitrarily many outside constraints lift exactly; this is unbounded in X.
Its geometric interpretation uses the original-position gap encoding. -/
theorem adjacent_inflation_context_iff {X : Type*}
    (R : X → Fin 4 → Fin 4 → Prop) (x : X) (s : Fin 8) :
    sixGapContext R x s ↔ fiveGapContext R x (gapInflationMap s) := by
  constructor
  · intro H g h hr
    exact (adjacent_inflation_gap_iff s g h).mp (H g h hr)
  · intro H g h hr
    exact (adjacent_inflation_gap_iff s g h).mpr (H g h hr)

/-- Exact complete-family transfer, retaining the outside configuration. -/
theorem adjacent_inflation_family_iff {X : Type*}
    (C : X → Prop) (R : X → Fin 4 → Fin 4 → Prop)
    (a b : X) (s t : Fin 5)
    (H : ∀ x q, C x ∧ fiveGapContext R x q ↔
      (x = a ∧ q = s) ∨ (x = b ∧ q = t)) :
    ∀ x q, C x ∧ sixGapContext R x q ↔
      (x = a ∧ gapInflationMap q = s) ∨
      (x = b ∧ gapInflationMap q = t) := by
  intro x q
  rw [adjacent_inflation_context_iff]
  exact H x (gapInflationMap q)

/-- Finite size dichotomy after exclusion of the two universal old states.
This is a count of local lifts, not by itself a theorem about game patterns. -/
theorem adjacent_inflation_pair_count : ∀ a b : Fin 3, a ≠ b →
    (Finset.univ.filter (fun q : Fin 8 =>
      (gapInflationMap q).val = a.val ∨ (gapInflationMap q).val = b.val)).card =
      if a = 2 ∨ b = 2 then 3 else 4 := by
  unfold gapInflationMap
  decide +kernel

#print axioms adjacent_inflation_gap_iff
#print axioms adjacent_inflation_context_iff
#print axioms adjacent_inflation_family_iff
#print axioms adjacent_inflation_two_family_regular
#print axioms adjacent_inflation_pair_count
end LC004
