import Flapjack.PanHHandleCallRet

/-!
# Parity checks for Pancake h_handle_call_ret_def

The direct HOL fixture in
scripts/hol-probes/pan_itree_h_handle_call_ret_probe.out is generated from
pan_itreeSemScript.sml:340-374.  These checks exercise failed, returned,
shape-error, exception, and caught-handler transitions.
-/

namespace Flapjack.Test.PanHHandleCallRetParity

open Flapjack

structure TestState where
  locals : VarName → Option (PanValue Nat)
  destination : Option (PanValue Nat)
  cleared : Bool

def hasWord (values : VarName → Option (PanValue Nat)) (name : VarName)
    (expected : Nat) : Bool :=
  match values name with
  | some (.word value) => value == expected
  | _ => false

def initialState : TestState :=
  { locals := updatePanValueMap (fun _ => none) "caller" (.word 3)
    destination := none
    cleared := false }

def context : PanHHandleCallContext Nat TestState where
  locals := fun state => state.locals
  setLocals := fun state locals => { state with locals := locals }
  emptyLocals := fun state => { state with locals := fun _ => none, cleared := true }
  setKvar := fun state kind name value =>
    match kind with
    | .local => { state with locals := updatePanValueMap state.locals name value }
    | .global => { state with destination := some value }
  isValidValue := fun _ _ _ _ => true
  exceptionShape := fun _ exception =>
    if exception == "E" then some .one else none

def returnNoCallType : Bool :=
  match panHHandleCallRet context none .one initialState
      (.returned (.returned (.word 7)) { initialState with locals := fun _ => none }) with
  | .ret (.returned (.word 7)) state => state.cleared && !hasWord state.locals "caller" 3
  | _ => false

def returnNoDestination : Bool :=
  match panHHandleCallRet context (some (none, none)) .one initialState
      (.returned (.returned (.word 7)) { initialState with locals := fun _ => none }) with
  | .ret .normal state => hasWord state.locals "caller" 3 && !state.cleared
  | _ => false

def returnShapeError : Bool :=
  match panHHandleCallRet context none (.comb []) initialState
      (.returned (.returned (.word 7)) initialState) with
  | .ret .error state => hasWord state.locals "caller" 3
  | _ => false

def failedPreservesCaller : Bool :=
  match panHHandleCallRet context none .one initialState .failed with
  | .ret .error state => hasWord state.locals "caller" 3
  | _ => false

def exceptionWithoutHandler : Bool :=
  match panHHandleCallRet context none .one initialState
      (.returned (.raised "E" (.word 8)) initialState) with
  | .ret (.raised "E" (.word 8)) state => state.cleared
  | _ => false

def caughtException : Bool :=
  let handler : Prog Nat := .skip
  match panHHandleCallRet context
      (some (none, some ("E", "exn", handler))) .one initialState
      (.returned (.raised "E" (.word 8)) { initialState with locals := fun _ => none }) with
  | .vis selected state k =>
      (match selected with | .skip => true | _ => false) &&
        hasWord state.locals "caller" 3 &&
        hasWord state.locals "exn" 8 &&
        match k .failed with
        | .ret .error _ => true
        | _ => false
  | _ => false

#guard returnNoCallType
#guard returnNoDestination
#guard returnShapeError
#guard failedPreservesCaller
#guard exceptionWithoutHandler
#guard caughtException

def runChecks : IO Bool := do
  if returnNoCallType then IO.println "PASS h_handle_call_ret return clears locals"
    else IO.println "FAIL h_handle_call_ret return clears locals"
  if returnNoDestination then IO.println "PASS h_handle_call_ret restores caller locals"
    else IO.println "FAIL h_handle_call_ret restores caller locals"
  if returnShapeError then IO.println "PASS h_handle_call_ret shape error"
    else IO.println "FAIL h_handle_call_ret shape error"
  if failedPreservesCaller then IO.println "PASS h_handle_call_ret failed caller state"
    else IO.println "FAIL h_handle_call_ret failed caller state"
  if exceptionWithoutHandler then IO.println "PASS h_handle_call_ret uncaught exception"
    else IO.println "FAIL h_handle_call_ret uncaught exception"
  if caughtException then IO.println "PASS h_handle_call_ret caught exception handler"
    else IO.println "FAIL h_handle_call_ret caught exception handler"
  pure (returnNoCallType && returnNoDestination && returnShapeError &&
    failedPreservesCaller && exceptionWithoutHandler && caughtException)

end Flapjack.Test.PanHHandleCallRetParity
