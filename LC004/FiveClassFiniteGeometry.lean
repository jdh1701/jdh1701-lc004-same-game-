import LC004.FiveClassGeometryBridge

namespace LC004

/-- Enumerate increasing endpoint pairs once, before testing for crossing. -/
def finiteOrderedPairs (xs : List Nat) : List (Nat × Nat) :=
  (xs ×ˢ xs).filter (fun uv => uv.1 < uv.2)

/-- Executable crossing predicate, proved equivalent to the game predicate. -/
def finiteBlockCross (xs ys : List Nat) : Bool :=
  (finiteOrderedPairs xs).any fun uv => (finiteOrderedPairs ys).any fun xy =>
    decide ((uv.1 < xy.1 ∧ xy.1 < uv.2 ∧ uv.2 < xy.2) ∨
      (xy.1 < uv.1 ∧ uv.1 < xy.2 ∧ xy.2 < uv.2))

theorem finiteBlockCross_iff (xs ys : List Nat) :
    finiteBlockCross xs ys = true ↔ BlocksCross xs ys := by
  simp only [finiteBlockCross, List.any_eq_true, finiteOrderedPairs,
    List.mem_filter, decide_eq_true_eq, Prod.exists, List.mem_product]
  constructor
  · rintro ⟨u, v, ⟨⟨hu,hv⟩, _⟩, x, y, ⟨⟨hx,hy⟩, _⟩, hc⟩
    exact ⟨u, hu, v, hv, x, hx, y, hy, hc⟩
  · rintro ⟨u, hu, v, hv, x, hx, y, hy, hc⟩
    have huv : u < v := by rcases hc with h | h <;> omega
    have hxy : x < y := by rcases hc with h | h <;> omega
    exact ⟨u, v, ⟨⟨hu,hv⟩, huv⟩, x, y, ⟨⟨hx,hy⟩, hxy⟩, hc⟩

/-- Lexicographic inventory of the ten two-element subsets of five ranks. -/
def fivePairRanks (s : Fin 10) : List Nat :=
  ![[0,1], [0,2], [0,3], [0,4], [1,2], [1,3], [1,4], [2,3], [2,4], [3,4]] s

def fiveSplitBlocks (g : List Nat) (s : Fin 10) : List (List Nat) :=
  [(fivePairRanks s).map (fun i => g[i]!),
   ((List.range 5).filter (fun i => !(fivePairRanks s).contains i)).map (fun i => g[i]!)]

def finiteNoncrossing (bs : List (List Nat)) : Bool :=
  bs.all fun a => bs.all fun b => !(finiteBlockCross a b)

theorem finiteNoncrossing_iff (bs : List (List Nat)) :
    finiteNoncrossing bs = true ↔ NoncrossingBlockFamily bs := by
  simp only [finiteNoncrossing, List.all_eq_true, Bool.not_eq_true', NoncrossingBlockFamily]
  simp only [← Bool.not_eq_true, Bool.not_eq_true', ← finiteBlockCross_iff]

def FiveCompatible (g h : List Nat) (x y : Fin 10) : Prop :=
  finiteNoncrossing (fiveSplitBlocks g x ++ fiveSplitBlocks h y) = true

instance (g h : List Nat) (x y : Fin 10) : Decidable (FiveCompatible g h x y) :=
  inferInstanceAs (Decidable (_ = true))

theorem fiveCompatible_iff (g h : List Nat) (x y : Fin 10) :
    FiveCompatible g h x y ↔
      NoncrossingBlockFamily (fiveSplitBlocks g x ++ fiveSplitBlocks h y) :=
  finiteNoncrossing_iff _

theorem choiceRelationClosed_empty {α β : Type*} [DecidableEq α] [DecidableEq β] :
    ChoiceRelationClosed (fun (_ : α) (_ : β) => False) := by
  intro _ _ _ _ _ _ h
  exact h.elim

theorem choiceRelationClosed_rectangle {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : α → Prop) (V : β → Prop) : ChoiceRelationClosed (fun x y => U x ∧ V y) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃ h₁ h₂ h₃
  unfold choiceMajority
  split_ifs <;> exact ⟨by first | exact h₁.1 | exact h₂.1,
    by first | exact h₁.2 | exact h₂.2⟩

theorem choiceRelationClosed_fan {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) : ChoiceRelationClosed (fun x y => x = a ∨ y = b) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃
  exact twoFan_closed_choiceMajority a b x₁ x₂ x₃ y₁ y₂ y₃

theorem choiceRelationClosed_inter {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R S : α → β → Prop} (hR : ChoiceRelationClosed R) (hS : ChoiceRelationClosed S) :
    ChoiceRelationClosed (fun x y => R x y ∧ S x y) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃ h₁ h₂ h₃
  exact ⟨hR _ _ _ _ _ _ h₁.1 h₂.1 h₃.1, hS _ _ _ _ _ _ h₁.2 h₂.2 h₃.2⟩

theorem choiceRelationClosed_twoPoints {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a c : α) (b d : β) :
    ChoiceRelationClosed (fun x y => (x = a ∧ y = b) ∨ (x = c ∧ y = d)) := by
  intro x₁ y₁ x₂ y₂ x₃ y₃ h₁ h₂ h₃
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h₃ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [choiceMajority]

theorem choiceRelationClosed_congr {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R S : α → β → Prop} (h : ∀ x y, R x y ↔ S x y) :
    ChoiceRelationClosed R ↔ ChoiceRelationClosed S := by
  unfold ChoiceRelationClosed
  simp only [h]

/-- A Boolean certificate avoids constructing a quantified decision proof for
all one hundred entries. Soundness is proved once in the kernel. -/
def finiteRelationMatches (B : Fin 10 → Fin 10 → Bool)
    (R : Fin 10 → Fin 10 → Prop) [DecidableRel R] : Bool :=
  (List.finRange 10).all fun x => (List.finRange 10).all fun y => B x y == decide (R x y)

theorem finiteRelationMatches_sound (B : Fin 10 → Fin 10 → Bool)
    (R : Fin 10 → Fin 10 → Prop) [DecidableRel R]
    (h : finiteRelationMatches B R = true) : ∀ x y, B x y = true ↔ R x y := by
  intro x y
  have hm := (List.all_eq_true.mp ((List.all_eq_true.mp h) x (List.mem_finRange x)))
    y (List.mem_finRange y)
  have hb : B x y = decide (R x y) := by simpa using hm
  rw [hb]
  simp only [decide_eq_true_eq]

def fiveOtherRanks (g : List Nat) : List Nat :=
  (List.range 10).filter (fun i => !g.contains i)

/-- The two local obligations required by abstract cancellation. -/
def FiveGeometryCase (g : List Nat) : Prop :=
  ChoiceRelationClosed (FiveCompatible g (fiveOtherRanks g)) ∧
    (BlocksCross g (fiveOtherRanks g) → ∃ p q : Fin 10,
      ∀ x y, FiveCompatible g (fiveOtherRanks g) x y → x = p ∨ y = q)

end LC004
