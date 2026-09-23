import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# PanSem `ExtCall` Error parity

HOL `panSem` (`cakeml/pancake/semantics/panSemScript.sml:716-729`) returns
`(SOME Error, s)` with the unchanged state when an `ExtCall` argument is not a
word or when the byte read fails.  These guards assert that the production
source evaluators return an explicit Error control result for both branches,
in the non-clocked (`evalPanValueFfiProgSteps`) and clocked
(`panSemEvaluateCodeStateWithPostState`) evaluators.

The HOL oracle is `scripts/hol-probes/pan_sem_extcall_error_probe.out`.
-/

namespace Flapjack.Test.PanSemExtCallErrorParity

open Flapjack Flapjack.RiscV

private abbrev Word64 := Word 64

def extState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3))
      else if name == "s" then some (.rStruct [])
      else none
    globals := fun name => if name == "g" then some (.word (BitVec.ofNat 64 4)) else none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel (domain := fun _ => false)

def nonwordProgram : Prog Word64 :=
  .extCall "f" (.var .local "s") (.const 0) (.const 0) (.const 0)

def readFailProgram : Prog Word64 :=
  .extCall "f" (.const 0) (.const 1) (.const 0) (.const 0)

def clockedEvaluate (clock : Nat) (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (extState clock) program
    (memoryAccess := memoryAccess)

def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 (extState 5).locals (extState 5).globals
    (extState 5).memory statefulTestFfiState program (memoryAccess := memoryAccess)

private def isWordOption (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isErrorAt (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) :
    Bool :=
  match result with
  | some ((.control (.error locals _ _ _), n), _) => n == clock && isWordOption 3 (locals "x")
  | _ => false

private def isErrorStepped (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals _ _ _, _) => isWordOption 3 (locals "x")
  | _ => false

def clockedNonwordGuard : Bool :=
  isErrorAt 5 (clockedEvaluate 5 nonwordProgram)

def clockedReadFailGuard : Bool :=
  isErrorAt 5 (clockedEvaluate 5 readFailProgram (some emptyAccess))

def nonClockedNonwordGuard : Bool :=
  isErrorStepped (nonClockedEvaluate nonwordProgram)

def nonClockedReadFailGuard : Bool :=
  isErrorStepped (nonClockedEvaluate readFailProgram (some emptyAccess))

def extCallErrorGuard : Bool :=
  clockedNonwordGuard && clockedReadFailGuard &&
    nonClockedNonwordGuard && nonClockedReadFailGuard

#guard extCallErrorGuard

def runChecks : IO Bool := do
  IO.println (if clockedNonwordGuard then
    "PASS panSem ExtCall non-word argument rejected with Error"
    else "FAIL panSem ExtCall non-word argument rejected with Error")
  IO.println (if clockedReadFailGuard then
    "PASS panSem ExtCall failed byte read rejected with Error"
    else "FAIL panSem ExtCall failed byte read rejected with Error")
  IO.println (if nonClockedNonwordGuard then
    "PASS non-clocked ExtCall non-word argument rejected with Error"
    else "FAIL non-clocked ExtCall non-word argument rejected with Error")
  IO.println (if nonClockedReadFailGuard then
    "PASS non-clocked ExtCall failed byte read rejected with Error"
    else "FAIL non-clocked ExtCall failed byte read rejected with Error")
  pure extCallErrorGuard

end Flapjack.Test.PanSemExtCallErrorParity