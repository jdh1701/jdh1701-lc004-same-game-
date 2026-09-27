import Std

namespace AlexandriaComplexity.RowElimination

/- Pointwise equation semantics for arbitrary assignments. This proves a row
operation and its list lifting, NOT the Python bitmask solver or its runtime. -/

structure Equation (Assignment : Type) where
  evaluate : Assignment → Bool
  rhs : Bool

def Holds {A : Type} (row : Equation A) (assignment : A) : Prop :=
  row.evaluate assignment = row.rhs

def HoldsAll {A : Type} : List (Equation A) → A → Prop
  | [], _ => True
  | row :: rows, assignment => Holds row assignment ∧ HoldsAll rows assignment

def addPivot {A : Type} (pivot row : Equation A) : Equation A where
  evaluate := fun assignment => Bool.xor (row.evaluate assignment) (pivot.evaluate assignment)
  rhs := Bool.xor row.rhs pivot.rhs

theorem bool_row_operation : ∀ (p r d b : Bool),
    (p = d ∧ r = b) ↔ (p = d ∧ Bool.xor r p = Bool.xor b d) := by
  decide

theorem row_operation {A : Type} (pivot row : Equation A) (assignment : A) :
    (Holds pivot assignment ∧ Holds row assignment) ↔
    (Holds pivot assignment ∧ Holds (addPivot pivot row) assignment) :=
  bool_row_operation (pivot.evaluate assignment) (row.evaluate assignment)
    pivot.rhs row.rhs

theorem system_operation {A : Type} (pivot : Equation A)
    (rows : List (Equation A)) (assignment : A)
    (hp : Holds pivot assignment) :
    HoldsAll rows assignment ↔ HoldsAll (rows.map (addPivot pivot)) assignment := by
  induction rows with
  | nil => exact Iff.rfl
  | cons row rows ih =>
      constructor
      · intro h
        exact ⟨((row_operation pivot row assignment).mp ⟨hp, h.1⟩).2,
          ih.mp h.2⟩
      · intro h
        exact ⟨((row_operation pivot row assignment).mpr ⟨hp, h.1⟩).2,
          ih.mpr h.2⟩

theorem satisfiability_preserved {A : Type} (pivot : Equation A)
    (rows : List (Equation A)) :
    (∃ assignment, Holds pivot assignment ∧ HoldsAll rows assignment) ↔
    (∃ assignment, Holds pivot assignment ∧
      HoldsAll (rows.map (addPivot pivot)) assignment) := by
  constructor
  · intro ⟨assignment, hp, hr⟩
    exact ⟨assignment, hp, (system_operation pivot rows assignment hp).mp hr⟩
  · intro ⟨assignment, hp, hr⟩
    exact ⟨assignment, hp, (system_operation pivot rows assignment hp).mpr hr⟩

theorem dropping_pivot_is_unsound :
    ¬ (∀ (p r d b : Bool), r = b ↔ Bool.xor r p = Bool.xor b d) := by
  decide

end AlexandriaComplexity.RowElimination
