import Mathlib.Data.List.Basic

namespace LC004

/-!
The grammar is the published Biedl et al. grammar, not a new recognizer.
This file proves a leftmost-block normal form and relabelling closure.
The equivalence with `OrdinarySolvable ordinaryStepAt` is NOT proved here.
-/

/-- S -> epsilon | SS | cSc | cScSc. -/
inductive ClickGrammar : List Nat → Prop
  | empty : ClickGrammar []
  | append {u v} : ClickGrammar u → ClickGrammar v → ClickGrammar (u ++ v)
  | pair (c) {u} : ClickGrammar u → ClickGrammar (c :: (u ++ [c]))
  | triple (c) {u v} : ClickGrammar u → ClickGrammar v →
      ClickGrammar (c :: (u ++ c :: (v ++ [c])))

/-- The block containing the first position is a pair or a triple.
The remaining intervals recurse independently. This removes associative
concatenation parses, but DOES NOT make different witnesses disjoint. -/
inductive FirstBlock : List Nat → Prop
  | empty : FirstBlock []
  | pair (c) {u v} : FirstBlock u → FirstBlock v →
      FirstBlock (c :: (u ++ c :: v))
  | triple (c) {u v z} : FirstBlock u → FirstBlock v → FirstBlock z →
      FirstBlock (c :: (u ++ c :: (v ++ c :: z)))

theorem firstBlock_append {u v : List Nat}
    (hu : FirstBlock u) (hv : FirstBlock v) : FirstBlock (u ++ v) := by
  induction hu with
  | empty => simpa using hv
  | pair c hu hz ihu ihz =>
      simpa [List.append_assoc] using FirstBlock.pair c hu ihz
  | triple c hu hw hz ihu ihw ihz =>
      simpa [List.append_assoc] using FirstBlock.triple c hu hw ihz

theorem clickGrammar_iff_firstBlock (w : List Nat) :
    ClickGrammar w ↔ FirstBlock w := by
  constructor
  · intro h
    induction h with
    | empty => exact FirstBlock.empty
    | append _ _ ihu ihv => exact firstBlock_append ihu ihv
    | pair c _ ihu => exact FirstBlock.pair c ihu FirstBlock.empty
    | triple c _ _ ihu ihv => exact FirstBlock.triple c ihu ihv FirstBlock.empty
  · intro h
    induction h with
    | empty => exact ClickGrammar.empty
    | pair c _ _ ihu ihv =>
        simpa [List.append_assoc] using (ClickGrammar.pair c ihu).append ihv
    | triple c _ _ _ ihu ihv ihz =>
        simpa [List.append_assoc] using (ClickGrammar.triple c ihu ihv).append ihz

/-- Identifying colours as well as renaming them preserves grammar membership.
No injectivity assumption is needed. -/
theorem clickGrammar_map (f : Nat → Nat) {w : List Nat}
    (h : ClickGrammar w) : ClickGrammar (w.map f) := by
  induction h with
  | empty => exact ClickGrammar.empty
  | append _ _ ihu ihv => simpa using ClickGrammar.append ihu ihv
  | pair c _ ihu => simpa using ClickGrammar.pair (f c) ihu
  | triple c _ _ ihu ihv => simpa using ClickGrammar.triple (f c) ihu ihv

#print axioms clickGrammar_iff_firstBlock
#print axioms clickGrammar_map

end LC004
