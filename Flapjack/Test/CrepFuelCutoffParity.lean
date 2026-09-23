import Flapjack.Test.CrepGlobalShapeParity

/-!
Fuel is an evaluator cutoff, not a semantic Crep `Error`. The recursive
sequence, call, and loop cases below pin that distinction. Bounded searches
also check that a suitable target-fuel witness exists for terminating runs.
-/

namespace Flapjack.Test.CrepFuelCutoffParity

open Flapjack
open Flapjack.Test.CrepGlobalShapeParity

def shortSequence : CrepProg Nat := .seq .skip .skip

/- At fuel one, the sequence's child has no fuel. -/
#guard (evalCrepRuntimeResult runtimeHandler noPrimitive 1 globalState
  shortSequence).isNone

/- A failed assignment is a semantic Error even when the supplied fuel is small. -/
#guard match evalCrepRuntimeResult runtimeHandler noPrimitive 1 globalState
    (.assign 99 (.const 1)) with
  | some (.error, _) => true
  | _ => false

/- Fuel exhaustion in the loop body remains a cutoff. -/
#guard (evalCrepRuntimeResult runtimeHandler noPrimitive 2 globalState
  (.while (.const 1) .skip)).isNone

def recursiveBody : CrepProg Nat := .call none "recur" []

def recursiveCallState : CrepRuntimeState Nat Unit :=
  { globalState with
    code := fun function =>
      if function == "recur" then some ([], recursiveBody) else none }

/- A recursive call whose callee body reaches zero fuel is still a cutoff. -/
#guard (evalCrepRuntimeResult runtimeHandler noPrimitive 1 recursiveCallState
  (.call none "recur" [])).isNone

/- A semantic Error reached inside a loop remains an Error result. -/
#guard match evalCrepRuntimeResult runtimeHandler noPrimitive 3 globalState
    (.while (.const 1) (.assign 99 (.const 2))) with
  | some (.error, _) => true
  | _ => false

#guard match evalCrepRuntimeResult runtimeHandler noPrimitive 3 globalState
    shortSequence with
  | some (.normal, _) => true
  | _ => false

def findsNormalFuel (fuelLimit : Nat) (program : CrepProg Nat) : Bool :=
  (List.range fuelLimit).any fun targetFuel =>
    match evalCrepRuntimeResult runtimeHandler noPrimitive targetFuel
        globalState program with
    | some (.normal, _) => true
    | _ => false

/- Bounded search witnesses ∃ targetFuel for the sequence. -/
#guard findsNormalFuel 4 shortSequence

def clockedLoop : CrepProg Nat := .while (.const 1) .skip

/- The loop reaches its semantic clock timeout with sufficient target fuel. -/
#guard match evalCrepRuntimeResult runtimeHandler noPrimitive 4 globalState
    clockedLoop with
  | some (.timeout, _) => true
  | _ => false

def findsTimeoutFuel (fuelLimit : Nat) (program : CrepProg Nat) : Bool :=
  (List.range fuelLimit).any fun targetFuel =>
    match evalCrepRuntimeResult runtimeHandler noPrimitive targetFuel
        globalState program with
    | some (.timeout, _) => true
    | _ => false

/- Bounded search witnesses ∃ targetFuel for the clocked loop timeout. -/
#guard findsTimeoutFuel 5 clockedLoop

/-- All fuel-cutoff distinctions above, as a single boolean checked at run time. -/
def fuelCutoffGuard : Bool :=
  (evalCrepRuntimeResult runtimeHandler noPrimitive 1 globalState
    shortSequence).isNone &&
  (match evalCrepRuntimeResult runtimeHandler noPrimitive 1 globalState
      (.assign 99 (.const 1)) with
    | some (.error, _) => true
    | _ => false) &&
  (evalCrepRuntimeResult runtimeHandler noPrimitive 2 globalState
    (.while (.const 1) .skip)).isNone &&
  (evalCrepRuntimeResult runtimeHandler noPrimitive 1 recursiveCallState
    (.call none "recur" [])).isNone &&
  (match evalCrepRuntimeResult runtimeHandler noPrimitive 3 globalState
      (.while (.const 1) (.assign 99 (.const 2))) with
    | some (.error, _) => true
    | _ => false) &&
  (match evalCrepRuntimeResult runtimeHandler noPrimitive 3 globalState
      shortSequence with
    | some (.normal, _) => true
    | _ => false) &&
  findsNormalFuel 4 shortSequence &&
  (match evalCrepRuntimeResult runtimeHandler noPrimitive 4 globalState
      clockedLoop with
    | some (.timeout, _) => true
    | _ => false) &&
  findsTimeoutFuel 5 clockedLoop

#guard fuelCutoffGuard

def runChecks : IO Bool := do
  if fuelCutoffGuard then
    IO.println "PASS crep fuel is cutoff not semantic error (seq/call/loop/timeout)"
  else
    IO.println "FAIL crep fuel cutoff distinctions"
  pure fuelCutoffGuard

end Flapjack.Test.CrepFuelCutoffParity
