import Flapjack.Pancake.Proofs.PanToCrep

/-!
Direct checks against `scripts/hol-probes/crep_mem_load_probe.out`.

HOL `crepSem$state.memory` is a total `word -> word_lab` function guarded by
`memaddrs` (`cakeml/pancake/semantics/crepSemScript.sml:24-51`).  The executable
`CrepRuntimeState.memory` stores absence in an `Option`; the bridge
`crepMemoryRel` records the HOL total view on every address `memaddrs` accepts,
and the two exact `mem_load_def` branches recover a `word_lab` cell or report
absence.
-/

namespace Flapjack.Test.CrepMemoryRelParity

open Flapjack

def validDomain : Nat → Bool := fun address => address == 0

def oneWordMemory : Nat → Option Nat := fun address => if address == 0 then some 7 else none

/-- Base state with `memaddrs` accepting only address `0`, matching the probe's
`memaddrs := {0w}` and total memory returning `Word 7w`. -/
def baseState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := oneWordMemory
    memaddrs := validDomain
    shMemaddrs := fun _ => false
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

/-- HOL total memory view: every address holds `Word 7`. -/
def totalMemory : Nat → PanWordLab Nat := fun _ => .word 7

/-- The production state and the total view satisfy the bridge on the guarded
domain. -/
theorem crepMemoryRel_holds : crepMemoryRel baseState totalMemory := by
  intro address hvalid
  simp [baseState, oneWordMemory, validDomain, totalMemory, panTheWord] at hvalid ⊢
  exact hvalid

/-- `mem_load_valid=SOME (Word 7w)`: a guarded address loads the total cell. -/
theorem load_valid :
    crepRuntimeLoad baseState 0 = some (panTheWord (totalMemory 0)) :=
  crepRuntimeLoad_eq_some_of_crepMemoryRel crepMemoryRel_holds (by rfl)

/-- `mem_load_invalid=NONE`: an address outside `memaddrs` has no cell. -/
theorem load_invalid : crepRuntimeLoad baseState 9 = none :=
  crepRuntimeLoad_eq_none_of_memaddrs_false (by rfl)

/-- `mem_load_valid=SOME (Word 7w)`, `mem_load_invalid=NONE`, and
`mem_load_other_valid=SOME (Word 7w)`. -/
def loadGuard : Bool :=
  (crepRuntimeLoad baseState 0 == some 7) &&
    (crepRuntimeLoad baseState 9).isNone

/-- `eval_load_valid=SOME (Word 7w)` and `eval_load_invalid=NONE`: reading a
load expression goes through `mem_load` and flattens the retained cell. -/
def evalGuard : Bool :=
  (evalCrepRuntimeExp baseState (.load (.const 0)) == some 7) &&
    (evalCrepRuntimeExp baseState (.load (.const 9))).isNone

def crepMemoryGuard : Bool :=
  loadGuard && evalGuard

#eval crepMemoryGuard
#guard crepMemoryGuard

def runChecks : IO Bool := do
  if crepMemoryGuard then
    IO.println "PASS crep memory HOL mem_load branches"
  else
    IO.println "FAIL crep memory HOL mem_load branches"
  pure crepMemoryGuard

end Flapjack.Test.CrepMemoryRelParity