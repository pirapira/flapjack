import Flapjack.Pancake.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`.  `expHdlFiniteMap` is the
faithful finite-map port; the executable adapter `expHdl` builds HOL's finite
map from the association-list compiler context (`infoMapToFiniteMap`) and calls
that port.  The duplicate fixtures pin the finite-map semantics: for both
`FUPDATE` and `FUPDATE_LIST` the last binding wins, and the executed adapter
must reproduce that on a duplicate-bearing context.
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

def threeWordVars : FiniteMap VarName (Shape × List Nat) :=
  FUPDATE FEMPTY ("x", (.one, [3, 4, 5]))

def threeWordOK : Bool :=
  match expHdlFiniteMap (α := Nat) threeWordVars "x" with
  | .seq (.assign 3 (.loadGlob 0))
      (.seq (.assign 4 (.loadGlob 1))
        (.seq (.assign 5 (.loadGlob 2)) .skip)) => true
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

/-! The compiler context stores bindings most-recent-first, so the association
    list whose finite-map replay is HOL's `FEMPTY |++ [(x,[3,4]); (x,[7])]` is
    the reversed list `[(x,[7]); (x,[3,4])]`.  The executed adapter must still
    emit the last-binding code, matching the HOL duplicate oracle. -/
def execDupVars : InfoMap (Shape × List Nat) :=
  [("x", (.one, [7])), ("x", (.one, [3, 4]))]

def execDupOK : Bool :=
  dupPattern (expHdl (α := Nat) execDupVars "x")

/-- The executable adapter's bridged finite map is exactly the HOL duplicate
    `FUPDATE_LIST` map, so its output equals the faithful port's. -/
example : expHdl (α := Nat) execDupVars "x" =
    expHdlFiniteMap (α := Nat) dupListVars "x" := rfl

def parityGuard : Bool :=
  missingOK && knownOK && threeWordOK && fmMissingOK && fmKnownOK && dupUpdateOK && dupListOK
    && execDupOK

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println
      "PASS exp_hdl missing, two-word, three-word, and duplicate-update global-load assignments"
  else
    IO.println "FAIL exp_hdl parity"
  pure parityGuard

end Flapjack.Test.ExpHdlParity
