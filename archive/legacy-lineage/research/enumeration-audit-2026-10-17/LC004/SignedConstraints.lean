import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

namespace LC004

/-!
Certified algebra for overlapping witnesses. `join` combines constraints;
the sole required semantic law is that satisfaction of a join is conjunction.
This law and the Same Game witness completeness theorem are separate obligations.
No game-specific assumptions are axioms in this file.
-/

abbrev SignedTerms (C : Type*) := List (ℤ × C)

def signedEval {C W : Type*} (sat : C → W → Prop)
    [DecidableRel sat] (terms : SignedTerms C) (w : W) : ℤ :=
  (terms.map fun t => if sat t.2 w then t.1 else 0).sum

/-- Add an event: old + new - intersection. Equal constraint keys may later
be collected without changing their evaluation. -/
def addConstraint {C : Type*} (join : C → C → C)
    (p : C) (terms : SignedTerms C) : SignedTerms C :=
  (1, p) :: (terms ++ terms.map (fun t => (-t.1, join t.2 p)))

def unionTerms {C : Type*} (join : C → C → C) : List C → SignedTerms C
  | [] => []
  | p :: ps => addConstraint join p (unionTerms join ps)

theorem signedEval_addConstraint {C W : Type*} (sat : C → W → Prop)
    [DecidableRel sat] (join : C → C → C)
    (hjoin : ∀ p r w, sat (join p r) w ↔ sat p w ∧ sat r w)
    (p : C) (terms : SignedTerms C) (w : W) :
    signedEval sat (addConstraint join p terms) w =
      if sat p w then 1 else signedEval sat terms w := by
  have hmap : signedEval sat (terms.map (fun t => (-t.1, join t.2 p))) w =
      if sat p w then -signedEval sat terms w else 0 := by
    induction terms with
    | nil => simp [signedEval]
    | cons t ts ih =>
        simp only [List.map_cons, signedEval, List.sum_cons] at ih ⊢
        by_cases hp : sat p w <;> by_cases ht : sat t.2 w <;>
          simp_all [hjoin] <;> ring
  simp only [addConstraint, signedEval, List.map_cons, List.map_append,
    List.sum_cons, List.sum_append]
  change (if sat p w then 1 else 0) +
    (signedEval sat terms w +
      signedEval sat (terms.map (fun t => (-t.1, join t.2 p))) w) = _
  rw [hmap]
  split_ifs <;> simp [signedEval]

/-- Every covered object contributes exactly one, however many witnesses it has.
Uncovered objects contribute zero. This is an all-input theorem, not a finite test. -/
theorem signedEval_unionTerms {C W : Type*} (sat : C → W → Prop)
    [DecidableRel sat] (join : C → C → C)
    (hjoin : ∀ p r w, sat (join p r) w ↔ sat p w ∧ sat r w)
    (ps : List C) (w : W) :
    signedEval sat (unionTerms join ps) w =
      if ∃ p ∈ ps, sat p w then 1 else 0 := by
  induction ps with
  | nil => simp [unionTerms, signedEval]
  | cons p ps ih =>
      rw [unionTerms, signedEval_addConstraint sat join hjoin, ih]
      by_cases hp : sat p w <;> simp [hp]

/-- Summing the certified pointwise identity counts the union once per object. -/
theorem signedEval_union_count {C W : Type*} [DecidableEq W]
    (sat : C → W → Prop) [DecidableRel sat] (join : C → C → C)
    (hjoin : ∀ p r w, sat (join p r) w ↔ sat p w ∧ sat r w)
    (ps : List C) (domain : Finset W) :
    ∑ w ∈ domain, signedEval sat (unionTerms join ps) w =
      ((domain.filter (fun w => ∃ p ∈ ps, sat p w)).card : ℤ) := by
  simp_rw [signedEval_unionTerms sat join hjoin]
  rw [← Finset.sum_filter]
  simp

/-- Move the finite sum over objects inside the signed constraint list. -/
theorem sum_signedEval {C W : Type*} [DecidableEq W]
    (sat : C → W → Prop) [DecidableRel sat]
    (terms : SignedTerms C) (domain : Finset W) :
    ∑ w ∈ domain, signedEval sat terms w =
      (terms.map fun t => t.1 *
        ((domain.filter (sat t.2)).card : ℤ)).sum := by
  induction terms with
  | nil => simp [signedEval]
  | cons t ts ih =>
      simp only [signedEval, List.map_cons, List.sum_cons] at ih ⊢
      rw [Finset.sum_add_distrib, ih]
      congr 1
      rw [← Finset.sum_filter]
      simp [mul_comm]

/-- Exact weighted union count. In the partition application, each individual
constraint has weight q raised to its number of equivalence classes. -/
theorem signed_constraint_count {C W : Type*} [DecidableEq W]
    (sat : C → W → Prop) [DecidableRel sat] (join : C → C → C)
    (hjoin : ∀ p r w, sat (join p r) w ↔ sat p w ∧ sat r w)
    (ps : List C) (domain : Finset W) :
    ((domain.filter (fun w => ∃ p ∈ ps, sat p w)).card : ℤ) =
      ((unionTerms join ps).map fun t => t.1 *
        ((domain.filter (sat t.2)).card : ℤ)).sum := by
  rw [← signedEval_union_count sat join hjoin, sum_signedEval]

#print axioms signedEval_addConstraint
#print axioms signedEval_unionTerms
#print axioms signedEval_union_count
#print axioms signed_constraint_count

end LC004
