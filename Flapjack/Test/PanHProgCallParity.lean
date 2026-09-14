import Flapjack.PanHProgCall

/-!
# Parity checks for Pancake h_prog_call_def
-/

namespace Flapjack.Test.PanHProgCallParity

open Flapjack

structure TestState where
  locals : VarName → Option (PanValue Nat)

def context : PanHProgCallContext Nat TestState where
  evalArguments := fun _ arguments =>
    if arguments.length == 1 then some [.word 7] else none
  lookupCode := fun _ function _ =>
    if function == "callee" then some (.skip, fun _ => none, .one) else none
  setLocals := fun state locals => { state with locals := locals }
  handleReturn :=
    { locals := fun state => state.locals
      setLocals := fun state locals => { state with locals := locals }
      emptyLocals := fun state => { state with locals := fun _ => none }
      setKvar := fun state _ _ _ => state
      isValidValue := fun _ _ _ _ => true
      exceptionShape := fun _ _ => none }

def sourceState : TestState := { locals := fun _ => none }

def argumentFailure : Bool :=
  match panHProgCall context none "callee" [] sourceState with
  | .ret .error _ => true
  | _ => false

def lookupFailure : Bool :=
  match panHProgCall context none "missing" [.const 7] sourceState with
  | .ret .error _ => true
  | _ => false

def successfulEvent : Bool :=
  match panHProgCall context none "callee" [.const 7] sourceState with
  | .vis selected state _ =>
      (match selected with | .skip => true | _ => false) &&
        match state.locals "missing" with
        | none => true
        | _ => false
  | _ => false

#guard argumentFailure
#guard lookupFailure
#guard successfulEvent

def runChecks : IO Bool := do
  if argumentFailure then IO.println "PASS h_prog_call argument failure"
    else IO.println "FAIL h_prog_call argument failure"
  if lookupFailure then IO.println "PASS h_prog_call lookup failure"
    else IO.println "FAIL h_prog_call lookup failure"
  if successfulEvent then IO.println "PASS h_prog_call callee event"
    else IO.println "FAIL h_prog_call callee event"
  pure (argumentFailure && lookupFailure && successfulEvent)

end Flapjack.Test.PanHProgCallParity
