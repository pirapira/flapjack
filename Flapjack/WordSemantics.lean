import Flapjack.RiscV.Backend

/-!
Call-aware executable semantics for the Word intermediate language.

The backend already evaluates individual Word functions. This module adds the
function-table boundary used by `loop_to_word`: arguments are read from the
caller registers, callee parameters are initialized in a fresh register
environment, returned values are assigned to the caller's declared registers,
and memory effects are carried back to the caller. Fuel bounds nested calls.
-/

namespace Flapjack.RiscV

def lookupWordFunction [NeZero width] :
    Nat → List (Nat × List Nat × WordProg (Word width)) →
      Option (List Nat × WordProg (Word width))
  | _, [] => none
  | label, (candidate, parameters, body) :: functions =>
      if label == candidate then some (parameters, body)
      else lookupWordFunction label functions

def clearWordRegisters [NeZero width] (state : State width) : State width :=
  { state with registers := fun _ => 0 }

def readWordRegisters [NeZero width] (state : State width) :
    List Nat → Option (List (Word width))
  | [] => some []
  | name :: names => do
      let register ← registerOfNat name
      let values ← readWordRegisters state names
      pure (readRegister state register :: values)

def bindWordRegisters [NeZero width] (state : State width)
    (names : List Nat) (values : List (Word width)) : Option (State width) :=
  if names.length != values.length then none
  else
    (names.zip values).foldl (fun result (name, value) => do
      let state ← result
      let register ← registerOfNat name
      pure (writeRegister state register value)) (some (clearWordRegisters state))

def assignWordRegisters [NeZero width] (state : State width)
    (names : List Nat) (values : List (Word width)) : Option (State width) :=
  if names.length != values.length then none
  else
    (names.zip values).foldl (fun result (name, value) => do
      let state ← result
      let register ← registerOfNat name
      pure (writeRegister state register value)) (some state)

mutual
  def evalWordCall [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → Option (List Nat × List Nat) → Option Nat → List Nat →
        Option (Nat × WordProg (Word width)) →
        Option (State width × List (Word width))
    | 0, _, _, _, _, _ => none
    | fuel + 1, state, returns, target, arguments, handler => do
        if handler.isSome then none
        else
          let target ← target
          let (parameters, body) ← lookupWordFunction target functions
          let values ← readWordRegisters state arguments
          let calleeState ← bindWordRegisters state parameters values
          let result ← evalWordFunctionWithCalls functions fuel calleeState body
          let returnedState := { state with
            memory := result.1.memory
            privilege := result.1.privilege
            mode := result.1.mode }
          match returns with
          | none => some (returnedState, result.2)
          | some (names, _) => do
              let state ← assignWordRegisters returnedState names result.2
              some (state, [])
    termination_by fuel _ _ _ _ _ => fuel

  def evalWordFunctionWithCalls [NeZero width]
      (functions : List (Nat × List Nat × WordProg (Word width))) :
      Nat → State width → WordProg (Word width) →
        Option (State width × List (Word width))
    | 0, _, _ => none
    | fuel + 1, state, .call returns target arguments handler =>
        evalWordCall functions fuel state returns target arguments handler
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFunctionWithCalls functions fuel state first
        if !result.2.isEmpty then some result
        else evalWordFunctionWithCalls functions fuel result.1 second
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFunctionWithCalls functions fuel state thenBranch
        else evalWordFunctionWithCalls functions fuel state elseBranch
    | fuel + 1, state, program => evalWordFunction state program
    termination_by fuel _ _ => fuel
end

/-!
An explicit host boundary for Word-level foreign calls.  The compiler keeps
the four FFI argument registers and the live-register list in the IR; the
target model cannot determine their external effect, so the handler is part
of the semantic environment.  Ordinary Word programs continue to use the
backend evaluator, while sequences and conditionals recurse through this
boundary.
-/
mutual
  def evalWordFfi [NeZero width]
      (handler : FunName → Word width → Word width → Word width → Word width →
        State width → Option (State width)) :
      Nat → State width → WordProg (Word width) →
        Option (State width × List (Word width))
    | 0, _, _ => none
    | fuel + 1, state,
        .ffi function configuration configurationLength array arrayLength _ => do
        let configuration ← registerOfNat configuration
        let configurationLength ← registerOfNat configurationLength
        let array ← registerOfNat array
        let arrayLength ← registerOfNat arrayLength
        let state ← handler function (readRegister state configuration)
          (readRegister state configurationLength) (readRegister state array)
          (readRegister state arrayLength) state
        pure (state, [])
    | fuel + 1, state, .seq first second => do
        let result ← evalWordFfi handler fuel state first
        if !result.2.isEmpty then some result
        else evalWordFfi handler fuel result.1 second
    | fuel + 1, state, .ite operator condition rightValue thenBranch elseBranch => do
        let choose ← evalWordCondition state operator condition rightValue
        if choose then evalWordFfi handler fuel state thenBranch
        else evalWordFfi handler fuel state elseBranch
    | fuel + 1, state, program => evalWordFunction state program
    termination_by fuel _ _ => fuel
end

theorem evalWordFfi_single [NeZero width]
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat) :
    evalWordFfi handler 1 state
        (.ffi function configuration configurationLength array arrayLength live) = (do
      let configuration ← registerOfNat configuration
      let configurationLength ← registerOfNat configurationLength
      let array ← registerOfNat array
      let arrayLength ← registerOfNat arrayLength
      let state ← handler function (readRegister state configuration)
        (readRegister state configurationLength) (readRegister state array)
        (readRegister state arrayLength) state
      pure (state, [])) := by
  simp [evalWordFfi]

end Flapjack.RiscV
