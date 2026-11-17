import LC004.NoncrossingBlockFamily
import LC004.ChoiceSupportedCancellation

namespace LC004

/-- Crossing depends only on the relative order of the positions. -/
theorem pairCross_strictMono_iff (f : Nat → Nat) (hf : StrictMono f)
    (u v x y : Nat) :
    PairCross (f u) (f v) (f x) (f y) ↔ PairCross u v x y := by
  simp only [PairCross, hf.lt_iff_lt]

/-- Transport the complete block crossing predicate, including unordered lists. -/
theorem blocksCross_map_strictMono_iff (f : Nat → Nat) (hf : StrictMono f)
    (xs ys : List Nat) :
    BlocksCross (xs.map f) (ys.map f) ↔ BlocksCross xs ys := by
  constructor
  · rintro ⟨u, hu, v, hv, x, hx, y, hy, h⟩
    obtain ⟨u, hu0, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v, hv0, rfl⟩ := List.mem_map.mp hv
    obtain ⟨x, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, hy0, rfl⟩ := List.mem_map.mp hy
    exact ⟨u, hu0, v, hv0, x, hx0, y, hy0,
      (pairCross_strictMono_iff f hf u v x y).mp h⟩
  · rintro ⟨u, hu, v, hv, x, hx, y, hy, h⟩
    exact ⟨f u, List.mem_map.mpr ⟨u, hu, rfl⟩,
      f v, List.mem_map.mpr ⟨v, hv, rfl⟩,
      f x, List.mem_map.mpr ⟨x, hx, rfl⟩,
      f y, List.mem_map.mpr ⟨y, hy, rfl⟩,
      (pairCross_strictMono_iff f hf u v x y).mpr h⟩

theorem noncrossingBlockFamily_map_strictMono_iff
    (f : Nat → Nat) (hf : StrictMono f) (blocks : List (List Nat)) :
    NoncrossingBlockFamily (blocks.map (List.map f)) ↔ NoncrossingBlockFamily blocks := by
  constructor
  · intro h a ha b hb hab
    exact h _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
      _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
      ((blocksCross_map_strictMono_iff f hf a b).mpr hab)
  · intro h a ha b hb hab
    obtain ⟨a, ha0, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb0, rfl⟩ := List.mem_map.mp hb
    exact h a ha0 b hb0 ((blocksCross_map_strictMono_iff f hf a b).mp hab)

/-- Finite rank compression needs order agreement only on the finite domain;
no extension of its embedding to all natural numbers is required. -/
theorem blocksCross_map_order_iff {α : Type*} (f g : α → Nat)
    (hfg : ∀ u v, f u < f v ↔ g u < g v) (xs ys : List α) :
    BlocksCross (xs.map f) (ys.map f) ↔ BlocksCross (xs.map g) (ys.map g) := by
  have hp : ∀ u v x y, PairCross (f u) (f v) (f x) (f y) ↔
      PairCross (g u) (g v) (g x) (g y) := by
    intros
    simp only [PairCross, hfg]
  constructor
  · rintro ⟨u, hu, v, hv, x, hx, y, hy, hc⟩
    obtain ⟨u, hu0, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v, hv0, rfl⟩ := List.mem_map.mp hv
    obtain ⟨x, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, hy0, rfl⟩ := List.mem_map.mp hy
    exact ⟨g u, List.mem_map.mpr ⟨u, hu0, rfl⟩,
      g v, List.mem_map.mpr ⟨v, hv0, rfl⟩,
      g x, List.mem_map.mpr ⟨x, hx0, rfl⟩,
      g y, List.mem_map.mpr ⟨y, hy0, rfl⟩, (hp u v x y).mp hc⟩
  · rintro ⟨u, hu, v, hv, x, hx, y, hy, hc⟩
    obtain ⟨u, hu0, rfl⟩ := List.mem_map.mp hu
    obtain ⟨v, hv0, rfl⟩ := List.mem_map.mp hv
    obtain ⟨x, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, hy0, rfl⟩ := List.mem_map.mp hy
    exact ⟨f u, List.mem_map.mpr ⟨u, hu0, rfl⟩,
      f v, List.mem_map.mpr ⟨v, hv0, rfl⟩,
      f x, List.mem_map.mpr ⟨x, hx0, rfl⟩,
      f y, List.mem_map.mpr ⟨y, hy0, rfl⟩, (hp u v x y).mpr hc⟩

theorem blocksCross_finite_rank_iff {n : Nat} (p : Fin n → Nat)
    (hp : StrictMono p) (xs ys : List (Fin n)) :
    BlocksCross (xs.map p) (ys.map p) ↔
      BlocksCross (xs.map Fin.val) (ys.map Fin.val) := by
  apply blocksCross_map_order_iff
  intro u v
  exact hp.lt_iff_lt

/-- With at least two coordinates, unary validity may be included in every
binary constraint. This permits ambient choices that never occur in a solution. -/
theorem unary_binary_spec_iff {ι : Type*} {D : ι → Type*} [Nontrivial ι]
    (U : ∀ i, D i → Prop) (R : ∀ i j, D i → D j → Prop) (a : ∀ i, D i) :
    ((∀ i, U i (a i)) ∧ (∀ i j, i ≠ j → R i j (a i) (a j))) ↔
      ∀ i j, i ≠ j → U i (a i) ∧ U j (a j) ∧ R i j (a i) (a j) := by
  constructor
  · rintro ⟨hU, hR⟩ i j hij
    exact ⟨hU i, hU j, hR i j hij⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨j, hj⟩ := exists_ne i
      exact (h i j (Ne.symm hj)).1
    · intro i j hij
      exact (h i j hij).2.2

#print axioms blocksCross_map_strictMono_iff
#print axioms noncrossingBlockFamily_map_strictMono_iff
#print axioms unary_binary_spec_iff
end LC004
