import Std

namespace AlexandriaComplexity.SpanReduction

/- Closure under zero and finite sums. For XOR this is linear span.
This certificate-level proof does not identify closure with V23's enumeration,
nor verify the Python bitmask implementation or its independence test. -/
inductive Span {A : Type} (zero : A) (add : A → A → A) (basis : List A) : A → Prop
  | zero : Span zero add basis zero
  | generator {x : A} : x ∈ basis → Span zero add basis x
  | combine {x y : A} : Span zero add basis x → Span zero add basis y →
      Span zero add basis (add x y)

theorem substitute_generators {A : Type} (z : A) (add : A → A → A)
    (source target : List A)
    (cover : ∀ x, x ∈ source → Span z add target x)
    (x : A) (h : Span z add source x) : Span z add target x := by
  induction h with
  | zero => exact Span.zero
  | generator hm => exact cover _ hm
  | combine _ _ ihx ihy => exact Span.combine ihx ihy

theorem mutual_coverage {A : Type} (z : A) (add : A → A → A)
    (source target : List A)
    (forward : ∀ x, x ∈ source → Span z add target x)
    (backward : ∀ x, x ∈ target → Span z add source x) (x : A) :
    Span z add source x ↔ Span z add target x :=
  ⟨substitute_generators z add source target forward x,
   substitute_generators z add target source backward x⟩

theorem drop_dependent {A : Type} (z : A) (add : A → A → A)
    (basis : List A) (v x : A) (hv : Span z add basis v) :
    Span z add (v :: basis) x ↔ Span z add basis x := by
  apply mutual_coverage z add (v :: basis) basis
  · intro y hy
    cases List.mem_cons.mp hy with
    | inl he => cases he; exact hv
    | inr hm => exact Span.generator hm
  · intro y hy
    exact Span.generator (List.mem_cons.mpr (Or.inr hy))

theorem drop_zero {A : Type} (z : A) (add : A → A → A)
    (basis : List A) (x : A) :
    Span z add (z :: basis) x ↔ Span z add basis x :=
  drop_dependent z add basis z x Span.zero

theorem predicate_preserved {A : Type} (z : A) (add : A → A → A)
    (source target : List A)
    (forward : ∀ x, x ∈ source → Span z add target x)
    (backward : ∀ x, x ∈ target → Span z add source x)
    (accept : A → Prop) :
    (∃ x, Span z add source x ∧ accept x) ↔
    (∃ x, Span z add target x ∧ accept x) := by
  constructor
  · intro ⟨x, hs, ha⟩
    exact ⟨x, (mutual_coverage z add source target forward backward x).mp hs, ha⟩
  · intro ⟨x, ht, ha⟩
    exact ⟨x, (mutual_coverage z add source target forward backward x).mpr ht, ha⟩

end AlexandriaComplexity.SpanReduction
