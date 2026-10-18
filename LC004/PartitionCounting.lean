import LC004.SignedConstraints
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.BigOperators

namespace LC004

/-!
Equality constraints are actual equivalence relations on word positions.
The join is taken in ALL equivalence relations, not in a noncrossing sublattice.
This file proves the q^blocks weight and the exact signed-union formula for any
finite list of partitions. It does not assert which partitions recognize Same Game.
-/

def Respects {n q : Nat} (p : Setoid (Fin n)) (w : Fin n → Fin q) : Prop :=
  p ≤ Setoid.ker w

theorem respects_join {n q : Nat} (p r : Setoid (Fin n)) (w : Fin n → Fin q) :
    Respects (p ⊔ r) w ↔ Respects p w ∧ Respects r w := sup_le_iff

noncomputable def blockCount {n : Nat} (p : Setoid (Fin n)) : Nat :=
  @Fintype.card (Quotient p) (Fintype.ofFinite _)

noncomputable def partitionEvent {n : Nat} (q : Nat) (p : Setoid (Fin n)) :
    Finset (Fin n → Fin q) := by
  classical
  exact Finset.univ.filter (Respects p)

/-- Assign one arbitrary colour per equivalence class. Different classes may
receive the same colour: this is q^blocks, not a falling factorial. -/
theorem card_partitionEvent {n : Nat} (q : Nat) (p : Setoid (Fin n)) :
    (partitionEvent q p).card = q ^ blockCount p := by
  classical
  letI : Fintype (Quotient p) := Fintype.ofFinite _
  rw [partitionEvent, ← Fintype.card_subtype]
  change Fintype.card {w : Fin n → Fin q // p ≤ Setoid.ker w} = _
  rw [Fintype.card_congr (Setoid.liftEquiv p), Fintype.card_fun]
  simp [blockCount]

noncomputable def coveredWords {n : Nat} (q : Nat) (ps : List (Setoid (Fin n))) :
    Finset (Fin n → Fin q) := by
  classical
  exact Finset.univ.filter (fun w => ∃ p ∈ ps, Respects p w)

/-- A universal exact polynomial evaluation for a union of equality events.
The finite witness list can contain duplicates or overlapping events. -/
theorem partition_union_count {n : Nat} (q : Nat) (ps : List (Setoid (Fin n))) :
    ((coveredWords q ps).card : ℤ) =
      ((unionTerms (· ⊔ ·) ps).map fun t => t.1 * (q : ℤ) ^ blockCount t.2).sum := by
  classical
  rw [coveredWords, signed_constraint_count Respects (· ⊔ ·) respects_join]
  congr 1
  apply List.map_congr_left
  intro t ht
  change t.1 * ((partitionEvent q t.2).card : ℤ) = _
  rw [card_partitionEvent]
  simp

#print axioms respects_join
#print axioms card_partitionEvent
#print axioms partition_union_count

end LC004
