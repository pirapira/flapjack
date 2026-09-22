import Flapjack.Pancake.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`.  `expHdlFiniteMap` is the
faithful finite-map port; the list-backed `expHdl` checks the existing
first-match executable helper.  The duplicate fixtures pin the finite-map
semantics: for both `FUPDATE` and `FUPDATE_LIST` the last binding wins.
-/

namespace Flapjack.Test.ExpHdlParity

open Flapjack

def vars : InfoMap (Shape × List Nat) := [("x", (.one, [3, 4]))]

def missingOK : Bool :=
  match expHdl (α := Nat) vars "missing" with
  | .skip => true
  | _ => false

def knownOK : Bool :=
  match expHdl (α := Nat) vars "x" with
  | .seq (.assign 3 (.loadGlob 0))
      (.seq (.assign 4 (.loadGlob 1)) .skip) => true
  | _ => false

def fmVars : FiniteMap VarName (Shape × List Nat) :=
  FUPDATE FEMPTY ("x", (.one, [3, 4]))

def dupUpdateVars : FiniteMap VarName (Shape × List Nat) :=
  FUPDATE (FUPDATE FEMPTY ("x", (.one, [3, 4]))) ("x", (.one, [7]))

def dupListVars : FiniteMap VarName (Shape × List Nat) :=
  FUPDATE_LIST FEMPTY [("x", (.one, [3, 4])), ("x", (.one, [7]))]

def fmMissingOK : Bool :=
  match expHdlFiniteMap (α := Nat) fmVars "missing" with
  | .skip => true
  | _ => false

def knownPattern : CrepProg Nat → Bool
  | .seq (.assign 3 (.loadGlob 0))
      (.seq (.assign 4 (.loadGlob 1)) .skip) => true
  | _ => false

def dupPattern : CrepProg Nat → Bool
  | .seq (.assign 7 (.loadGlob 0)) .skip => true
  | _ => false

def fmKnownOK : Bool := knownPattern (expHdlFiniteMap (α := Nat) fmVars "x")

def dupUpdateOK : Bool :=
  dupPattern (expHdlFiniteMap (α := Nat) dupUpdateVars "x")

def dupListOK : Bool :=
  dupPattern (expHdlFiniteMap (α := Nat) dupListVars "x")

def parityGuard : Bool :=
  missingOK && knownOK && fmMissingOK && fmKnownOK && dupUpdateOK && dupListOK

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println
      "PASS exp_hdl missing/known global-load assignments; duplicate finite-map updates keep the last binding"
  else
    IO.println "FAIL exp_hdl parity"
  pure parityGuard

end Flapjack.Test.ExpHdlParity
