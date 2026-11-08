import AlexandriaComplexity.Resolution

namespace AlexandriaComplexity

/-!
A finite graph-parity foundation for Tseitin contradictions.

Each edge has two endpoints inside a fixed finite vertex set.  An edge
assignment toggles both endpoint bits when that edge is selected.  The
resulting boundary vector therefore always has even global XOR parity.

This is the parity layer underlying Tseitin contradictions.  It does not yet
encode the local parity constraints as CNF, prove a Resolution width lower
bound, or imply any unrestricted complexity-class separation.
-/

def xorBool : Bool → Bool → Bool
  | false, value => value
  | true, value => !value

def xorList : List Bool → Bool
  | [] => false
  | value :: tail => xorBool value (xorList tail)

def zeroBits : Nat → List Bool
  | 0 => []
  | n + 1 => false :: zeroBits n

def toggleAt : Nat → List Bool → List Bool
  | _, [] => []
  | 0, value :: tail => (!value) :: tail
  | index + 1, value :: tail => value :: toggleAt index tail

theorem length_zeroBits (n : Nat) :
    (zeroBits n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n inductionHypothesis =>
      change Nat.succ (zeroBits n).length = Nat.succ n
      rw [inductionHypothesis]

theorem xor_zeroBits (n : Nat) :
    xorList (zeroBits n) = false := by
  induction n with
  | zero =>
      rfl
  | succ n inductionHypothesis =>
      change xorList (zeroBits n) = false
      exact inductionHypothesis

theorem length_toggleAt (index : Nat) (bits : List Bool) :
    (toggleAt index bits).length = bits.length := by
  induction bits generalizing index with
  | nil =>
      cases index <;> rfl
  | cons value tail inductionHypothesis =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          change Nat.succ (toggleAt index tail).length = Nat.succ tail.length
          rw [inductionHypothesis]

theorem xorList_toggleAt
    (index : Nat)
    (bits : List Bool)
    (valid : index < bits.length) :
    xorList (toggleAt index bits) = !xorList bits := by
  induction bits generalizing index with
  | nil =>
      cases valid
  | cons value tail inductionHypothesis =>
      cases index with
      | zero =>
          change xorBool (!value) (xorList tail) =
            !(xorBool value (xorList tail))
          cases value <;> cases xorList tail <;> rfl
      | succ index =>
          have tailValid : index < tail.length :=
            Nat.lt_of_succ_lt_succ valid
          change
            xorBool value (xorList (toggleAt index tail)) =
              !(xorBool value (xorList tail))
          rw [inductionHypothesis index tailValid]
          cases value <;> cases xorList tail <;> rfl

theorem xorList_togglePair
    (first second : Nat)
    (bits : List Bool)
    (firstValid : first < bits.length)
    (secondValid : second < bits.length) :
    xorList (toggleAt second (toggleAt first bits)) = xorList bits := by
  have secondAfterFirst :
      second < (toggleAt first bits).length := by
    rw [length_toggleAt]
    exact secondValid
  rw [xorList_toggleAt second (toggleAt first bits) secondAfterFirst]
  rw [xorList_toggleAt first bits firstValid]
  cases xorList bits <;> rfl

structure Edge (vertexCount : Nat) where
  first : Nat
  second : Nat
  firstValid : first < vertexCount
  secondValid : second < vertexCount

structure FiniteGraph where
  vertexCount : Nat
  edges : List (Edge vertexCount)

def applyEdgesFrom
    {vertexCount : Nat}
    (index : Nat)
    (edges : List (Edge vertexCount))
    (assignment : Nat → Bool)
    (state : List Bool) : List Bool :=
  match edges with
  | [] => state
  | edge :: tail =>
      match assignment index with
      | false => applyEdgesFrom (index + 1) tail assignment state
      | true =>
          applyEdgesFrom (index + 1) tail assignment
            (toggleAt edge.second (toggleAt edge.first state))

theorem length_applyEdgesFrom
    {vertexCount : Nat}
    (index : Nat)
    (edges : List (Edge vertexCount))
    (assignment : Nat → Bool)
    (state : List Bool) :
    (applyEdgesFrom index edges assignment state).length = state.length := by
  induction edges generalizing index state with
  | nil =>
      rfl
  | cons edge tail inductionHypothesis =>
      unfold applyEdgesFrom
      cases selected : assignment index with
      | false =>
          exact inductionHypothesis (index + 1) state
      | true =>
          rw [inductionHypothesis]
          rw [length_toggleAt, length_toggleAt]

theorem xor_applyEdgesFrom
    {vertexCount : Nat}
    (index : Nat)
    (edges : List (Edge vertexCount))
    (assignment : Nat → Bool)
    (state : List Bool)
    (stateLength : state.length = vertexCount) :
    xorList (applyEdgesFrom index edges assignment state) = xorList state := by
  induction edges generalizing index state with
  | nil =>
      rfl
  | cons edge tail inductionHypothesis =>
      unfold applyEdgesFrom
      cases selected : assignment index with
      | false =>
          exact inductionHypothesis (index + 1) state stateLength
      | true =>
          have firstValid : edge.first < state.length := by
            rw [stateLength]
            exact edge.firstValid
          have secondValid : edge.second < state.length := by
            rw [stateLength]
            exact edge.secondValid
          let nextState :=
            toggleAt edge.second (toggleAt edge.first state)
          have nextLength : nextState.length = vertexCount := by
            unfold nextState
            rw [length_toggleAt, length_toggleAt, stateLength]
          have tailInvariant :
              xorList (applyEdgesFrom (index + 1) tail assignment nextState) =
                xorList nextState :=
            inductionHypothesis (index + 1) nextState nextLength
          rw [tailInvariant]
          unfold nextState
          exact xorList_togglePair edge.first edge.second state firstValid secondValid

def boundary
    (graph : FiniteGraph)
    (assignment : Nat → Bool) : List Bool :=
  applyEdgesFrom 0 graph.edges assignment (zeroBits graph.vertexCount)

theorem boundary_even
    (graph : FiniteGraph)
    (assignment : Nat → Bool) :
    xorList (boundary graph assignment) = false := by
  unfold boundary
  rw [xor_applyEdgesFrom 0 graph.edges assignment
    (zeroBits graph.vertexCount) (length_zeroBits graph.vertexCount)]
  exact xor_zeroBits graph.vertexCount

def SatisfiesTseitin
    (graph : FiniteGraph)
    (assignment : Nat → Bool)
    (charges : List Bool) : Prop :=
  boundary graph assignment = charges

def OddCharge (charges : List Bool) : Prop :=
  xorList charges = true

theorem odd_charge_unsatisfiable
    (graph : FiniteGraph)
    (charges : List Bool)
    (odd : OddCharge charges) :
    ¬ ∃ assignment, SatisfiesTseitin graph assignment charges := by
  intro witness
  rcases witness with ⟨assignment, satisfied⟩
  have evenBoundary : xorList (boundary graph assignment) = false :=
    boundary_even graph assignment
  unfold SatisfiesTseitin at satisfied
  rw [satisfied] at evenBoundary
  unfold OddCharge at odd
  rw [odd] at evenBoundary
  cases evenBoundary

end AlexandriaComplexity
