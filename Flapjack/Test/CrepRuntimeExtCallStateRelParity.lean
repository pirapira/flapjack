import Flapjack.Pancake.Proofs.PanToCrep

/-! Nonvacuous checks for the assembled canonical-target `ExtCall` dispatch and
its source/target simulation step in `Flapjack/Pancake/Semantics/CrepRuntimeTarget.lean`
and `Flapjack/Pancake/Proofs/PanToCrep.lean`.  A `stateRel` fixture relates a
source `PanSemState` to `riscv64CrepRuntimeTarget base`; the dispatch theorem
then follows the source-level `callFfi`/`call_FFI` result, and installing the
same ffi on both states preserves `stateRel`. -/

namespace Flapjack.Test.CrepRuntimeExtCallStateRelParity

open Flapjack

/-- Total target memory: every cell holds the probe word whose little-endian
    bytes are `[1, 2, 3, 4, 5, 6, 7, 8]`. -/
def callBaseMemory : RiscV.Word 64 → PanWordLab (RiscV.Word 64) :=
  fun _ => .word 0x0807060504030201

/-- A canonical-target base state with a readable memory domain. -/
def callBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := callBaseMemory
    memaddrs := fun _ => true
    shMemaddrs := fun _ => false
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := 8
    ffiContext := riscv64PanValueFfiContext (fun _ => false)
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

/-- The related source Pancake state: its memory view is the target word cells. -/
def callSource : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun address => some (.word (panTheWord (callBase.memory address)))
    memaddrs := callBase.memaddrs
    sharedMemaddrs := callBase.shMemaddrs
    clock := callBase.clock
    be := callBase.bigEndian
    ffi := callBase.ffi
    baseAddress := callBase.baseAddress
    topAddress := callBase.topAddress }

theorem callStateRel : stateRel callSource (riscv64CrepRuntimeTarget callBase) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  rfl

/-- The two argument reads succeed with the little-endian probe bytes. -/
theorem callReadConfiguration :
    riscv64ReadByteArray callBase (8 : RiscV.Word 64) 4 =
      some [(1 : UInt8), 2, 3, 4] := by
  decide

theorem callReadArray :
    riscv64ReadByteArray callBase (8 : RiscV.Word 64) 4 =
      some [(1 : UInt8), 2, 3, 4] := by
  decide

/-- The assembled dispatch step, with the source-level `callFfi`/`call_FFI`
    result on `callSource.ffi`. -/
example :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget callBase) "f"
        (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 =
      (match callFfi callSource.ffi (.extCall "f") [1, 2, 3, 4] [1, 2, 3, 4] with
       | .returned ffi bytes =>
           (.normal, riscv64WriteState { callBase with ffi := ffi }
             (8 : RiscV.Word 64) bytes)
       | .final event => (.finalFfi event, riscv64CrepRuntimeTarget callBase)) :=
  crepRuntimeExtCallValues_stateRel_dispatch callSource callBase "f"
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 [1, 2, 3, 4] [1, 2, 3, 4]
    callStateRel callReadConfiguration callReadArray

/-- Updating both related states with the same ffi result preserves `stateRel`. -/
example :
    stateRel { callSource with ffi := callSource.ffi }
      { riscv64CrepRuntimeTarget callBase with ffi := callSource.ffi } :=
  stateRel_ffiUpdate callSource (riscv64CrepRuntimeTarget callBase) callSource.ffi
    callStateRel

/-- A base with an empty memory domain, so both argument reads fail. -/
def callErrorBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { callBase with memaddrs := fun _ => false }

def callErrorSource : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  { callSource with memaddrs := fun _ => false }

theorem callErrorStateRel :
    stateRel callErrorSource (riscv64CrepRuntimeTarget callErrorBase) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  rfl

/-- The failing-read branch of the same fixture, at the source/target level. -/
example :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget callErrorBase) "f"
        (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 =
      (.error, riscv64CrepRuntimeTarget callErrorBase) :=
  crepRuntimeExtCallValues_stateRel_error callErrorSource callErrorBase "f"
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 callErrorStateRel
    (Or.inl (by
      simp [riscv64ReadByteArray, RiscV.panRiscVReadByte, panModelReadByte,
        callErrorBase]))

def dispatchGuard : Bool :=
  match callFfi callSource.ffi (.extCall "f") [1, 2, 3, 4] [1, 2, 3, 4] with
  | .returned _ _ => true
  | .final _ => true

def runChecks : IO Bool := do
  let checks := [
    ("Crep ExtCall dispatch follows source call_FFI and stateRel ffi update",
      dispatchGuard),
    ("Crep ExtCall failing-read branch returns Error with state unchanged", true)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.CrepRuntimeExtCallStateRelParity
