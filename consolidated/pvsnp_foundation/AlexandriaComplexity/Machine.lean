namespace AlexandriaComplexity

/-!
A small deterministic-machine semantics for the C1 foundation.  Execution is
indexed by explicit fuel.  These definitions and lemmas concern exact finite
execution only; they state no asymptotic runtime bound and no class separation.
-/

inductive HeadMove where
  | left
  | stay
  | right
deriving DecidableEq, Repr

inductive TapeSymbol where
  | blank
  | zero
  | one
deriving DecidableEq, Repr

def encodeBit : Bool → TapeSymbol
  | false => .zero
  | true => .one

def decodeSymbol : TapeSymbol → Option Bool
  | .blank => none
  | .zero => some false
  | .one => some true

def encodeWord : List Bool → List TapeSymbol
  | [] => []
  | bit :: tail => encodeBit bit :: encodeWord tail

def decodeWord : List TapeSymbol → Option (List Bool)
  | [] => some []
  | symbol :: tail => do
      let bit ← decodeSymbol symbol
      let decodedTail ← decodeWord tail
      pure (bit :: decodedTail)

structure MachineConfiguration (State : Type) where
  state : State
  tape : Int → TapeSymbol
  head : Int

structure DeterministicMachine (State : Type) where
  transition : State → TapeSymbol → State × TapeSymbol × HeadMove
  halt : State → Option Bool

def writeTape (tape : Int → TapeSymbol) (head : Int)
    (symbol : TapeSymbol) : Int → TapeSymbol :=
  fun position => if position = head then symbol else tape position

def moveHead (head : Int) : HeadMove → Int
  | .left => head - 1
  | .stay => head
  | .right => head + 1

def DeterministicMachine.step {State : Type} (machine : DeterministicMachine State)
    (configuration : MachineConfiguration State) : MachineConfiguration State :=
  match machine.halt configuration.state with
  | some _ => configuration
  | none =>
      let action := machine.transition configuration.state
        (configuration.tape configuration.head)
      {
        state := action.1
        tape := writeTape configuration.tape configuration.head action.2.1
        head := moveHead configuration.head action.2.2
      }

def DeterministicMachine.runFor {State : Type} (machine : DeterministicMachine State) :
    Nat → MachineConfiguration State → MachineConfiguration State
  | 0, configuration => configuration
  | fuel + 1, configuration => machine.step (machine.runFor fuel configuration)

def DeterministicMachine.acceptsWithin {State : Type}
    (machine : DeterministicMachine State) (fuel : Nat)
    (configuration : MachineConfiguration State) : Prop :=
  machine.halt (machine.runFor fuel configuration).state = some true

theorem writeTape_at (tape : Int → TapeSymbol) (head : Int) (symbol : TapeSymbol) :
    writeTape tape head symbol head = symbol := by
  exact if_pos rfl

theorem decodeWord_encodeWord : ∀ input : List Bool,
    decodeWord (encodeWord input) = some input
  | [] => rfl
  | false :: tail => by
      change Option.bind (decodeWord (encodeWord tail))
        (fun decodedTail => some (false :: decodedTail)) = some (false :: tail)
      rw [decodeWord_encodeWord tail]
      rfl
  | true :: tail => by
      change Option.bind (decodeWord (encodeWord tail))
        (fun decodedTail => some (true :: decodedTail)) = some (true :: tail)
      rw [decodeWord_encodeWord tail]
      rfl

theorem encodeWord_injective : Function.Injective encodeWord := by
  intro left right equalEncoding
  have equalDecoding := congrArg decodeWord equalEncoding
  rw [decodeWord_encodeWord left, decodeWord_encodeWord right] at equalDecoding
  exact Option.some.inj equalDecoding

theorem writeTape_away (tape : Int → TapeSymbol) (head position : Int)
    (symbol : TapeSymbol)
    (different : position ≠ head) :
    writeTape tape head symbol position = tape position := by
  exact if_neg different

theorem step_halted {State : Type} (machine : DeterministicMachine State)
    (configuration : MachineConfiguration State) (result : Bool)
    (halted : machine.halt configuration.state = some result) :
    machine.step configuration = configuration := by
  unfold DeterministicMachine.step
  rw [halted]

theorem runFor_halted {State : Type} (machine : DeterministicMachine State)
    (configuration : MachineConfiguration State) (result : Bool)
    (halted : machine.halt configuration.state = some result) :
    ∀ fuel, machine.runFor fuel configuration = configuration := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change machine.step (machine.runFor fuel configuration) = configuration
      rw [inductionHypothesis]
      exact step_halted machine configuration result halted

theorem acceptsWithin_succ {State : Type} (machine : DeterministicMachine State)
    (fuel : Nat) (configuration : MachineConfiguration State)
    (accepted : machine.acceptsWithin fuel configuration) :
    machine.acceptsWithin (Nat.succ fuel) configuration := by
  unfold DeterministicMachine.acceptsWithin at accepted ⊢
  change machine.halt (machine.step (machine.runFor fuel configuration)).state = some true
  have fixed : machine.step (machine.runFor fuel configuration) =
      machine.runFor fuel configuration :=
    step_halted machine (machine.runFor fuel configuration) true accepted
  rw [fixed]
  exact accepted

theorem acceptsWithin_add {State : Type} (machine : DeterministicMachine State)
    (fuel extra : Nat) (configuration : MachineConfiguration State)
    (accepted : machine.acceptsWithin fuel configuration) :
    machine.acceptsWithin (fuel + extra) configuration := by
  induction extra with
  | zero => simpa
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact acceptsWithin_succ machine (fuel + extra) configuration inductionHypothesis

end AlexandriaComplexity
