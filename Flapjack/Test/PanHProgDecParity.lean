import Flapjack.PanHProgDec

/-!
# Parity checks for Pancake `h_prog_dec_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_dec_probe.out` comes from
`pan_itreeSemScript.sml:226-238`.  These checks exercise successful
declaration events, restoration of the saved local binding, evaluation
failure, shape failure, and the exceptional subprogram response.
-/

namespace Flapjack.Test.PanHProgDecParity

open Flapjack

structure DecState where
  token : Nat
  locals : VarName → Option (PanValue Nat)

def initialLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 3) else none

def initialState : DecState :=
  { token := 7, locals := initialLocals }

def decContext : PanHProgDecContext Nat DecState where
  eval := fun state expression =>
    match expression with
    | .const value => some (.word value)
    | .var .local name => state.locals name
    | _ => none
  localValue := fun state name => state.locals name
  extendLocal := fun state name value =>
    { state with locals := updatePanValueMap state.locals name value }
  restoreLocal := fun state name oldValue =>
    { state with locals := panValueResVar state.locals name oldValue }

def body : Prog Nat := .return (.const 0)

def validTree : PanHProgDecTree Nat DecState :=
  panHProgDec [] decContext initialState "x" .one (.const 7) body

def missingTree : PanHProgDecTree Nat DecState :=
  panHProgDec [] decContext initialState "x" .one
    (.var .local "missing") .skip

def wrongShapeTree : PanHProgDecTree Nat DecState :=
  panHProgDec [] decContext initialState "x" (.comb []) (.const 7) .skip

def isWord (value : Option (PanValue Nat)) (expected : Nat) : Bool :=
  match value with
  | some (.word value) => value == expected
  | _ => false

def observeEventAndRestore : Bool :=
  match validTree with
  | .vis returnedBody extended k =>
      (match returnedBody with
       | .return (.const 0) => true
       | _ => false) &&
        isWord (extended.locals "x") 7 &&
        match k (.returned .normal extended) with
        | .ret .normal restored =>
            restored.token == 7 && isWord (restored.locals "x") 3
        | _ => false
  | _ => false

def observeFailureResponse : Bool :=
  match validTree with
  | .vis _ _ k =>
      match k .failed with
      | .ret .error state => state.token == 7 && isWord (state.locals "x") 3
      | _ => false
  | _ => false

def observeMissing : Bool :=
  match missingTree with
  | .ret .error state => state.token == 7
  | _ => false

def observeWrongShape : Bool :=
  match wrongShapeTree with
  | .ret .error state => state.token == 7
  | _ => false

#guard observeEventAndRestore
#guard observeFailureResponse
#guard observeMissing
#guard observeWrongShape

def runChecks : IO Bool := do
  if observeEventAndRestore then
    IO.println "PASS h_prog_dec program event and local restoration"
  else
    IO.println "FAIL h_prog_dec program event and local restoration"
  if observeFailureResponse then
    IO.println "PASS h_prog_dec exceptional subprogram response"
  else
    IO.println "FAIL h_prog_dec exceptional subprogram response"
  if observeMissing then
    IO.println "PASS h_prog_dec missing expression"
  else
    IO.println "FAIL h_prog_dec missing expression"
  if observeWrongShape then
    IO.println "PASS h_prog_dec shape failure"
  else
    IO.println "FAIL h_prog_dec shape failure"
  pure (observeEventAndRestore && observeFailureResponse && observeMissing &&
    observeWrongShape)

end Flapjack.Test.PanHProgDecParity
