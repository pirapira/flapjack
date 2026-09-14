import Flapjack.PanHProgDecCall

/-!
# Parity checks for Pancake h_prog_deccall_def

The checks cover argument evaluation failure, code lookup failure, and the
successful callee program event with the declaration return handler attached.
-/

namespace Flapjack.Test.PanHProgDecCallParity

open Flapjack

structure TestState where
  locals : VarName → Option (PanValue Nat)

def context : PanHProgDecCallContext Nat TestState where
  evalArguments := fun _ arguments =>
    if arguments.length == 1 then some [.word 7] else none
  lookupCode := fun _ function _ =>
    if function == "callee" then some (.skip, fun _ => none, .one) else none
  setLocals := fun state locals => { state with locals := locals }
  handleReturn :=
    { locals := fun state => state.locals
      setLocals := fun state locals => { state with locals := locals }
      emptyLocals := fun state => { state with locals := fun _ => none }
      setLocal := fun state name value =>
        { state with locals := updatePanValueMap state.locals name value }
      restoreLocal := fun state name oldValue =>
        { state with locals := restorePanValueLocal state.locals name oldValue } }

def sourceState : TestState := { locals := fun _ => none }

def argumentFailure : Bool :=
  match panHProgDecCall context "result" .one "callee" [] .skip sourceState with
  | .ret .error _ => true
  | _ => false

def lookupFailure : Bool :=
  match panHProgDecCall context "result" .one "missing" [.const 7] .skip sourceState with
  | .ret .error _ => true
  | _ => false

def successfulEvent : Bool :=
  match panHProgDecCall context "result" .one "callee" [.const 7] .skip sourceState with
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
  if argumentFailure then IO.println "PASS h_prog_deccall argument failure"
    else IO.println "FAIL h_prog_deccall argument failure"
  if lookupFailure then IO.println "PASS h_prog_deccall lookup failure"
    else IO.println "FAIL h_prog_deccall lookup failure"
  if successfulEvent then IO.println "PASS h_prog_deccall callee event"
    else IO.println "FAIL h_prog_deccall callee event"
  pure (argumentFailure && lookupFailure && successfulEvent)

end Flapjack.Test.PanHProgDecCallParity
