import Flapjack.PanHProgCall

/-!
# Parity checks for Pancake `h_prog_call_def`

The direct HOL fixture in `scripts/hol-probes/pan_itree_h_prog_call_probe.out`
is generated from `pan_itreeSemScript.sml:377-385`.  The Lean checks cover
argument failure, lookup failure, and the successful callee event with the
source-created locals.
-/

namespace Flapjack.Test.PanHProgCallParity

open Flapjack

structure TestState where
  locals : VarName → Option (PanValue Nat)
  cleared : Bool

def hasWord (values : VarName → Option (PanValue Nat)) (name : VarName)
    (expected : Nat) : Bool :=
  match values name with
  | some (.word value) => value == expected
  | _ => false

def initialState : TestState :=
  { locals := updatePanValueMap (fun _ => none) "caller" (.word 3)
    cleared := false }

def handleContext : PanHHandleCallContext Nat TestState where
  locals := fun state => state.locals
  setLocals := fun state locals => { state with locals := locals }
  emptyLocals := fun state => { state with locals := fun _ => none, cleared := true }
  setKvar := fun state _ name value =>
    { state with locals := updatePanValueMap state.locals name value }
  isValidValue := fun _ _ _ _ => true
  exceptionShape := fun _ _ => none

def successContext : PanHProgCallContext Nat TestState where
  evalArguments := fun _ _ => some [.word 1]
  lookupCode := fun _ function _ =>
    if function == "callee" then
      some (.skip, updatePanValueMap (fun _ => none) "arg" (.word 1), .one)
    else none
  setLocals := fun state locals => { state with locals := locals }
  handleReturn := handleContext

def evalFailureContext : PanHProgCallContext Nat TestState where
  evalArguments := fun _ _ => none
  lookupCode := fun _ _ _ => none
  setLocals := fun state locals => { state with locals := locals }
  handleReturn := handleContext

def lookupFailureContext : PanHProgCallContext Nat TestState where
  evalArguments := fun _ _ => some [.word 1]
  lookupCode := fun _ _ _ => none
  setLocals := fun state locals => { state with locals := locals }
  handleReturn := handleContext

def observeEvalFailure : Bool :=
  match panHProgCall evalFailureContext none "callee" [] initialState with
  | .ret .error state => hasWord state.locals "caller" 3
  | _ => false

def observeLookupFailure : Bool :=
  match panHProgCall lookupFailureContext none "missing" [] initialState with
  | .ret .error state => hasWord state.locals "caller" 3
  | _ => false

def observeSuccess : Bool :=
  match panHProgCall successContext none "callee" [] initialState with
  | .vis .skip state continuation =>
      hasWord state.locals "arg" 1 &&
        match continuation .failed with
        | .ret .error _ => true
        | _ => false
  | _ => false

#guard observeEvalFailure
#guard observeLookupFailure
#guard observeSuccess

def runChecks : IO Bool := do
  if observeEvalFailure then IO.println "PASS h_prog_call argument failure"
    else IO.println "FAIL h_prog_call argument failure"
  if observeLookupFailure then IO.println "PASS h_prog_call lookup failure"
    else IO.println "FAIL h_prog_call lookup failure"
  if observeSuccess then IO.println "PASS h_prog_call callee event and locals"
    else IO.println "FAIL h_prog_call callee event and locals"
  pure (observeEvalFailure && observeLookupFailure && observeSuccess)

end Flapjack.Test.PanHProgCallParity
