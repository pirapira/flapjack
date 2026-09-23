import Flapjack.Pancake.Semantics.CrepSem

/-!
Direct runtime checks against `scripts/hol-probes/crep_locals_wordlab_probe.out`.
Cake's `crepSem` locals are indexed by `varname` and store `word_lab` cells;
`set_var` writes a `Word w` wrapper and `eval` of a `Var` returns that wrapped
cell unchanged, while `upd_locals`/repeated `set_var` keep the last write.
-/

namespace Flapjack.Test.CrepLocalsWordLabParity

open Flapjack

def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0
def noNatDomain : Nat → Bool := fun _ => false

/-- Base state with an empty local map, matching the probe's `s with locals :=
FEMPTY`. -/
def baseState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

def setThree : Nat → Option (PanWordLab Nat) :=
  updateCrepRuntimeLocal (fun _ => none) 3 (.word 7)

/-- `locals_set_var_cell=SOME (Word 7w)` and
`locals_set_var_other_absent=NONE`. -/
def cellGuard : Bool :=
  setThree 3 == some (.word 7) && (setThree 9).isNone

/-- `locals_eval_var=SOME (Word 7w)` and `locals_eval_var_missing=NONE`: the
cell is retained and a `Var` read flattens it through `panTheWord`. -/
def evalGuard : Bool :=
  evalCrepRuntimeExp { baseState with locals := setThree } (.var 3) == some 7 &&
    (evalCrepRuntimeExp { baseState with locals := setThree } (.var 9)).isNone

/-- `locals_upd_locals_cells=(SOME (Word 5w),SOME (Word 7w))`. -/
def updGuard : Bool :=
  match assignCrepRuntimeLocals (fun _ => none) [2, 3] [5, 7] with
  | some locals => locals 2 == some (.word 5) && locals 3 == some (.word 7)
  | none => false

/-- `locals_set_var_overwrite=SOME (Word 9w)`: the last write wins. -/
def overwriteGuard : Bool :=
  updateCrepRuntimeLocal (updateCrepRuntimeLocal (fun _ => none) 3 (.word 7)) 3 (.word 9) 3 ==
    some (.word 9)

def localsWordLabGuard : Bool :=
  cellGuard && evalGuard && updGuard && overwriteGuard

#eval localsWordLabGuard
#guard localsWordLabGuard

def runChecks : IO Bool := do
  if localsWordLabGuard then
    IO.println "PASS crep locals HOL word_lab cell shape"
  else
    IO.println "FAIL crep locals HOL word_lab cell shape"
  pure localsWordLabGuard

end Flapjack.Test.CrepLocalsWordLabParity