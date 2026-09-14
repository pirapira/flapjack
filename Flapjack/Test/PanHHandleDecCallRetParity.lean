import Flapjack.PanHHandleDecCallRet

/-!
# Parity checks for Pancake h_handle_deccall_ret_def

The checks cover both shape checks, result-variable installation, restoration
on a normal handler response, source-state failure, and exception propagation.
-/

namespace Flapjack.Test.PanHHandleDecCallRetParity

open Flapjack

structure TestState where
  locals : VarName → Option (PanValue Nat)
  cleared : Bool

def hasWord (values : VarName → Option (PanValue Nat)) (name : VarName)
    (expected : Nat) : Bool :=
  match values name with
  | some (.word value) => value == expected
  | _ => false

def missing (values : VarName → Option (PanValue Nat)) (name : VarName) : Bool :=
  match values name with
  | none => true
  | _ => false

def initialState : TestState :=
  { locals := updatePanValueMap (fun _ => none) "caller" (.word 3)
    cleared := false }

def context : PanHHandleDecCallContext Nat TestState where
  locals := fun state => state.locals
  setLocals := fun state locals => { state with locals := locals }
  emptyLocals := fun state => { state with locals := fun _ => none, cleared := true }
  setLocal := fun state name value =>
    { state with locals := updatePanValueMap state.locals name value }
  restoreLocal := fun state name oldValue =>
    { state with locals := restorePanValueLocal state.locals name oldValue }

def returnedHandler : Prog Nat := .skip

def returnedAndRestored : Bool :=
  match panHHandleDecCallRet context "result" .one returnedHandler .one initialState
      (.returned (.returned (.word 8))
        { initialState with locals := fun _ => none }) with
  | .vis selected state k =>
      (match selected with | .skip => true | _ => false) &&
        hasWord state.locals "caller" 3 &&
        hasWord state.locals "result" 8 &&
        match k (.returned .normal state) with
        | .ret .normal restored => hasWord restored.locals "caller" 3 &&
            missing restored.locals "result"
        | _ => false
  | _ => false

def shapeMismatch : Bool :=
  match panHHandleDecCallRet context "result" (.comb []) returnedHandler .one initialState
      (.returned (.returned (.word 8)) initialState) with
  | .ret .error _ => true
  | _ => false

def failedSourceState : Bool :=
  match panHHandleDecCallRet context "result" .one returnedHandler .one initialState .failed with
  | .ret .error state => hasWord state.locals "caller" 3
  | _ => false

def raisedClearsLocals : Bool :=
  match panHHandleDecCallRet context "result" .one returnedHandler .one initialState
      (.returned (.raised "E" (.word 9)) initialState) with
  | .ret (.raised "E" (.word 9)) state => state.cleared
  | _ => false

#guard returnedAndRestored
#guard shapeMismatch
#guard failedSourceState
#guard raisedClearsLocals

def runChecks : IO Bool := do
  if returnedAndRestored then IO.println "PASS h_handle_deccall_ret installs/restores result"
    else IO.println "FAIL h_handle_deccall_ret installs/restores result"
  if shapeMismatch then IO.println "PASS h_handle_deccall_ret shape mismatch"
    else IO.println "FAIL h_handle_deccall_ret shape mismatch"
  if failedSourceState then IO.println "PASS h_handle_deccall_ret failed source state"
    else IO.println "FAIL h_handle_deccall_ret failed source state"
  if raisedClearsLocals then IO.println "PASS h_handle_deccall_ret raised clears locals"
    else IO.println "FAIL h_handle_deccall_ret raised clears locals"
  pure (returnedAndRestored && shapeMismatch && failedSourceState && raisedClearsLocals)

end Flapjack.Test.PanHHandleDecCallRetParity
