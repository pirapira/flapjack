import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake semantic `If` result

The source oracles are `scripts/hol-probes/pan_sem_ite_e2e_probe.out` and
`scripts/hol-probes/pan_sem_ite_memory_probe.out`, generated from
`panSemScript.sml:617-620`. They pin `If` outcomes against the production
evaluator:

* a nonzero word condition runs the then branch (clock unchanged);
* a zero word condition runs the else branch (clock unchanged);
* a non-word (unbound) condition is rejected with `SOME Error` and the
  unchanged state;
* a condition whose own evaluation fails (a load from an empty memory domain)
  is rejected with `SOME Error` and the unchanged state;
* with a memory-reading condition owned by the source state, a present nonzero
  cell selects the then branch, a present zero cell selects the else branch, an
  address outside `memaddrs` is rejected with `SOME Error`, and the same cell
  selects different branches under little- versus big-endian byte reads.
-/

namespace Flapjack.Test.PanSemIteParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def iteState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def iteEvaluate (clock : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (iteState clock) program

def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

def isNormalAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.normal _ _ _ _), n), _) => n == clock
  | _ => false

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def thenAssign : Prog Word64 := .assign .local "x" (.const (BitVec.ofNat 64 9))

def trueIte : Prog Word64 := .ite (.const (BitVec.ofNat 64 1)) thenAssign .skip

def falseIte : Prog Word64 := .ite (.const (BitVec.ofNat 64 0)) thenAssign .skip

def nonwordIte : Prog Word64 := .ite (.var .local "z") thenAssign .skip

def failIte : Prog Word64 :=
  .ite (.load .one (.const (BitVec.ofNat 64 0))) thenAssign .skip

/-! ### Memory-reading conditions owned by the source state

    `memIteState` records a cell at address `8` and puts `8` in `memaddrs`;
    the memory access is derived from the state (`panSemBitVec64MemoryAccess`)
    so the domain and `be` inputs drive the byte reads. -/

def memIteState (memory : Word64 → Option (PanValue Word64)) (be : Bool)
    (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := memory
    memaddrs := fun address => address == BitVec.ofNat 64 8
    sharedMemaddrs := fun _ => false
    clock := clock
    be := be
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def memIteEvaluate (state : PanSemState Word64 (FfiState Unit))
    (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) state program
    (memoryAccess := some (panSemBitVec64MemoryAccess state))

def memNonzeroMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x1122334455667788))
    else some (.word (BitVec.ofNat 64 0))

def memZeroMemory : Word64 → Option (PanValue Word64) :=
  fun _ => some (.word (BitVec.ofNat 64 0))

def memHighByteMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x8800000000000000))
    else some (.word (BitVec.ofNat 64 0))

def memThenElseProgram (address : Word64) : Prog Word64 :=
  .ite (.load .one (.const address)) thenAssign
    (.assign .local "x" (.const (BitVec.ofNat 64 0)))

def memByteProgram : Prog Word64 :=
  .ite (.loadByte (.const (BitVec.ofNat 64 8))) thenAssign
    (.assign .local "x" (.const (BitVec.ofNat 64 0)))

def memNonzeroState : PanSemState Word64 (FfiState Unit) :=
  memIteState memNonzeroMemory false 5

def memZeroState : PanSemState Word64 (FfiState Unit) :=
  memIteState memZeroMemory false 5

def memLittleEndianState : PanSemState Word64 (FfiState Unit) :=
  memIteState memHighByteMemory false 5

def memBigEndianState : PanSemState Word64 (FfiState Unit) :=
  memIteState memHighByteMemory true 5

def memIteNonzeroGuard : Bool :=
  isNormalAt 5 (memIteEvaluate memNonzeroState (memThenElseProgram (BitVec.ofNat 64 8))) &&
    (match memIteEvaluate memNonzeroState (memThenElseProgram (BitVec.ofNat 64 8)) with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 9 (locals "x")
     | _ => false)

def memIteZeroGuard : Bool :=
  isNormalAt 5 (memIteEvaluate memZeroState (memThenElseProgram (BitVec.ofNat 64 8))) &&
    (match memIteEvaluate memZeroState (memThenElseProgram (BitVec.ofNat 64 8)) with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 0 (locals "x")
     | _ => false)

def memIteDomainGuard : Bool :=
  isErrorAt 5 (memIteEvaluate memNonzeroState (memThenElseProgram (BitVec.ofNat 64 9))) &&
    (match memIteEvaluate memNonzeroState (memThenElseProgram (BitVec.ofNat 64 9)) with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def memIteByteLEGuard : Bool :=
  isNormalAt 5 (memIteEvaluate memLittleEndianState memByteProgram) &&
    (match memIteEvaluate memLittleEndianState memByteProgram with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 0 (locals "x")
     | _ => false)

def memIteByteBEGuard : Bool :=
  isNormalAt 5 (memIteEvaluate memBigEndianState memByteProgram) &&
    (match memIteEvaluate memBigEndianState memByteProgram with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 9 (locals "x")
     | _ => false)

def iteTrueGuard : Bool :=
  isNormalAt 5 (iteEvaluate 5 trueIte) &&
    (match iteEvaluate 5 trueIte with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 9 (locals "x")
     | _ => false)

def iteFalseGuard : Bool :=
  isNormalAt 5 (iteEvaluate 5 falseIte) &&
    (match iteEvaluate 5 falseIte with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteNonwordGuard : Bool :=
  isErrorAt 5 (iteEvaluate 5 nonwordIte) &&
    (match iteEvaluate 5 nonwordIte with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteFailGuard : Bool :=
  isErrorAt 5 (iteEvaluate 5 failIte) &&
    (match iteEvaluate 5 failIte with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteGuard : Bool :=
  iteTrueGuard && iteFalseGuard && iteNonwordGuard && iteFailGuard &&
    memIteNonzeroGuard && memIteZeroGuard && memIteDomainGuard &&
    memIteByteLEGuard && memIteByteBEGuard

#guard iteGuard

def runChecks : IO Bool := do
  if iteTrueGuard then
    IO.println "PASS panSem If nonzero condition runs then branch"
  else IO.println "FAIL panSem If nonzero condition runs then branch"
  if iteFalseGuard then
    IO.println "PASS panSem If zero condition runs else branch"
  else IO.println "FAIL panSem If zero condition runs else branch"
  if iteNonwordGuard then
    IO.println "PASS panSem If non-word condition rejected with Error and unchanged state"
  else IO.println "FAIL panSem If non-word condition rejected with Error and unchanged state"
  if iteFailGuard then
    IO.println "PASS panSem If failing condition rejected with Error and unchanged state"
  else IO.println "FAIL panSem If failing condition rejected with Error and unchanged state"
  if memIteNonzeroGuard then
    IO.println "PASS panSem If memory condition nonzero cell runs then branch"
  else IO.println "FAIL panSem If memory condition nonzero cell runs then branch"
  if memIteZeroGuard then
    IO.println "PASS panSem If memory condition zero cell runs else branch"
  else IO.println "FAIL panSem If memory condition zero cell runs else branch"
  if memIteDomainGuard then
    IO.println "PASS panSem If memory condition outside domain rejected with Error"
  else IO.println "FAIL panSem If memory condition outside domain rejected with Error"
  if memIteByteLEGuard then
    IO.println "PASS panSem If little-endian byte condition runs else branch"
  else IO.println "FAIL panSem If little-endian byte condition runs else branch"
  if memIteByteBEGuard then
    IO.println "PASS panSem If big-endian byte condition runs then branch"
  else IO.println "FAIL panSem If big-endian byte condition runs then branch"
  pure iteGuard

end Flapjack.Test.PanSemIteParity
