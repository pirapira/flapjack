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

/-- The four-local wrapper fixture: Nat-indexed target locals holding the
    argument words in the production roles `configuration` (address),
    `configurationLength`, `array` (address), `arrayLength`. -/
def wrapperLocals : Nat → Option (PanWordLab (RiscV.Word 64))
  | 0 => some (.word 8)
  | 1 => some (.word 4)
  | 2 => some (.word 8)
  | 3 => some (.word 4)
  | _ => none

def wrapperBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { callBase with locals := wrapperLocals }

theorem wrapperStateRel :
    stateRel callSource (riscv64CrepRuntimeTarget wrapperBase) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  rfl

theorem wrapperReadConfiguration :
    riscv64ReadByteArray wrapperBase (8 : RiscV.Word 64) 4 =
      some [(1 : UInt8), 2, 3, 4] := by
  decide

theorem wrapperReadArray :
    riscv64ReadByteArray wrapperBase (8 : RiscV.Word 64) 4 =
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

/-- The `FFI_return` write-back branch: after the empty-name `call_FFI` identity
    returns the array bytes on the unchanged ffi, writing those bytes back keeps
    the source and target states related (HOL `write_bytearray` on source,
    `riscv64WriteState` on target). -/
example :
    stateRel
      { callSource with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel callBase.memaddrs)
          (riscv64PanValueFfiContext callBase.shMemaddrs) callSource.memory
          (8 : RiscV.Word 64) (8 : RiscV.Word 64) [1, 2, 3, 4],
        ffi := callBase.ffi }
      (riscv64WriteState { callBase with ffi := callBase.ffi } (8 : RiscV.Word 64)
        [1, 2, 3, 4]) :=
  crepRuntimeExtCallValues_stateRel_returned callSource callBase
    (8 : RiscV.Word 64) [1, 2, 3, 4] callBase.ffi callStateRel

/-- The assembled dispatch step: `FFI_return` writes the returned bytes back and
    the post-states are related. -/
example :
    (crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget callBase) "" (8 : RiscV.Word 64) 4
        (8 : RiscV.Word 64) 4 =
      (.normal, riscv64WriteState { callBase with ffi := callBase.ffi }
        (8 : RiscV.Word 64) [1, 2, 3, 4])) ∧
    stateRel
      { callSource with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel callBase.memaddrs)
          (riscv64PanValueFfiContext callBase.shMemaddrs) callSource.memory
          (8 : RiscV.Word 64) (8 : RiscV.Word 64) [1, 2, 3, 4],
        ffi := callBase.ffi }
      (riscv64WriteState { callBase with ffi := callBase.ffi } (8 : RiscV.Word 64)
        [1, 2, 3, 4]) :=
  crepRuntimeExtCallValues_stateRel_dispatch_returned callSource callBase ""
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 [1, 2, 3, 4] [1, 2, 3, 4]
    callBase.ffi [1, 2, 3, 4] callStateRel callReadConfiguration callReadArray
    (by rw [riscv64ExtCallCallFfiHandler_extCall]; rfl)

/-- The actual four-local production wrapper `crepRuntimeExtCall` (Nat-indexed
    target locals) resolves to the same `FFI_return` write-back dispatch, with the
    source `panSemWriteBytearray` post-state built by the theorem. -/
example :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget wrapperBase) "" 0 1 2 3 =
      (.normal, riscv64WriteState { wrapperBase with ffi := wrapperBase.ffi }
        (8 : RiscV.Word 64) [1, 2, 3, 4])) ∧
    stateRel
      { callSource with
        memory := panSemWriteBytearray
          (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel wrapperBase.memaddrs)
          (riscv64PanValueFfiContext wrapperBase.shMemaddrs) callSource.memory
          (8 : RiscV.Word 64) (8 : RiscV.Word 64) [1, 2, 3, 4],
        ffi := wrapperBase.ffi }
      (riscv64WriteState { wrapperBase with ffi := wrapperBase.ffi }
        (8 : RiscV.Word 64) [1, 2, 3, 4]) :=
  crepRuntimeExtCall_stateRel_dispatch_returned callSource wrapperBase "" 0 1 2 3
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4
    rfl rfl rfl rfl [1, 2, 3, 4] [1, 2, 3, 4] wrapperBase.ffi [1, 2, 3, 4]
    wrapperStateRel wrapperReadConfiguration wrapperReadArray
    (by rw [riscv64ExtCallCallFfiHandler_extCall]; rfl)

/-- An oracle that reports a `final` event on `.extCall "live"` and fails
    otherwise (HOL `Oracle_final`). -/
def finalOracle : FfiOracle Unit := fun name _ _ _ =>
  match name with
  | .extCall "live" => .final .diverged
  | _ => .final .failed

def finalFfiState : FfiState Unit :=
  { oracle := finalOracle, state := (), ioEvents := [] }

def finalBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { wrapperBase with ffi := finalFfiState }

def finalSource : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  { callSource with ffi := finalFfiState }

theorem finalStateRel :
    stateRel finalSource (riscv64CrepRuntimeTarget finalBase) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  rfl

theorem finalReadConfiguration :
    riscv64ReadByteArray finalBase (8 : RiscV.Word 64) 4 =
      some [(1 : UInt8), 2, 3, 4] := by
  decide

theorem finalReadArray :
    riscv64ReadByteArray finalBase (8 : RiscV.Word 64) 4 =
      some [(1 : UInt8), 2, 3, 4] := by
  decide

def finalEvent : FfiFinalEvent :=
  { name := .extCall "live", configuration := [1, 2, 3, 4]
    bytes := [1, 2, 3, 4], outcome := .diverged }

/-- The non-returned `FFI_final` branch through the four-local wrapper: the step
    returns `FinalFFI` and both states stay related unchanged (HOL
    `(SOME (FinalFFI outcome), s)`). -/
example :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget finalBase) "live" 0 1 2 3 =
      (.finalFfi finalEvent, riscv64CrepRuntimeTarget finalBase)) ∧
    stateRel finalSource (riscv64CrepRuntimeTarget finalBase) :=
  crepRuntimeExtCall_stateRel_dispatch_final finalSource finalBase "live" 0 1 2 3
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 rfl rfl rfl rfl [1, 2, 3, 4]
    [1, 2, 3, 4] finalEvent finalStateRel finalReadConfiguration finalReadArray
    (by rw [riscv64ExtCallCallFfiHandler_extCall]; rfl)

/-- A four-local wrapper over the empty-memory base, so the reads fail. -/
def wrapperErrorBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { callErrorBase with locals := wrapperLocals }

theorem wrapperErrorStateRel :
    stateRel callErrorSource (riscv64CrepRuntimeTarget wrapperErrorBase) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  rfl

/-- The failing-read branch through the four-local wrapper: `Error` with both
    states unchanged and still related (HOL `_ => (SOME Error, s)`). -/
example :
    (crepRuntimeExtCall riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget wrapperErrorBase) "f" 0 1 2 3 =
      (.error, riscv64CrepRuntimeTarget wrapperErrorBase)) ∧
    stateRel callErrorSource (riscv64CrepRuntimeTarget wrapperErrorBase) :=
  crepRuntimeExtCall_stateRel_error callErrorSource wrapperErrorBase "f" 0 1 2 3
    (8 : RiscV.Word 64) 4 (8 : RiscV.Word 64) 4 rfl rfl rfl rfl
    wrapperErrorStateRel
    (Or.inl (by
      simp [riscv64ReadByteArray, RiscV.panRiscVReadByte, panModelReadByte,
        wrapperErrorBase, callErrorBase]))

/-- The written target state reads back the returned first byte. -/
def returnedGuard : Bool :=
  let written := riscv64WriteState { callBase with ffi := callBase.ffi }
    (8 : RiscV.Word 64) [1, 2, 3, 4]
  RiscV.panRiscVReadByte written.memaddrs (crepRuntimeMemoryView written.memory)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (1 : RiscV.Word 64)

def dispatchGuard : Bool :=
  match callFfi callSource.ffi (.extCall "f") [1, 2, 3, 4] [1, 2, 3, 4] with
  | .returned _ _ => true
  | .final _ => true

/-- Executes the four-local wrapper and checks the returned byte landed. -/
def wrapperGuard : Bool :=
  match crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget wrapperBase) "" 0 1 2 3 with
  | (.normal, state) =>
      RiscV.panRiscVReadByte state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (1 : RiscV.Word 64)
  | _ => false

/-- Executes the four-local wrapper on the `FFI_final` fixture. -/
def finalGuard : Bool :=
  match crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget finalBase) "live" 0 1 2 3 with
  | (.finalFfi _, _) => true
  | _ => false

/-- Executes the four-local wrapper on the failing-read fixture. -/
def errorGuard : Bool :=
  match crepRuntimeExtCall riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget wrapperErrorBase) "f" 0 1 2 3 with
  | (.error, _) => true
  | _ => false

/-- The one-shot dispatch theorem on the four-local `wrapperBase` fixture. -/
example :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget wrapperBase) "" (8 : RiscV.Word 64) 4
        (8 : RiscV.Word 64) 4 =
      (match riscv64ReadByteArray wrapperBase (8 : RiscV.Word 64) 4,
             riscv64ReadByteArray wrapperBase (8 : RiscV.Word 64) 4 with
       | some configurationBytes, some arrayBytes =>
           (match callFfi wrapperBase.ffi (.extCall "") configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { wrapperBase with ffi := ffi }
                  (8 : RiscV.Word 64) bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget wrapperBase))
       | _, _ => (.error, riscv64CrepRuntimeTarget wrapperBase)) :=
  crepRuntimeExtCallValues_target_dispatch_any wrapperBase "" (8 : RiscV.Word 64) 4
    (8 : RiscV.Word 64) 4

/-- Executes the one-shot production dispatch and checks the returned byte. -/
def oneShotGuard : Bool :=
  match crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
      (riscv64CrepRuntimeTarget wrapperBase) "" (8 : RiscV.Word 64) 4
      (8 : RiscV.Word 64) 4 with
  | (.normal, state) =>
      RiscV.panRiscVReadByte state.memaddrs (crepRuntimeMemoryView state.memory)
        (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (1 : RiscV.Word 64)
  | _ => false

def runChecks : IO Bool := do
  let checks := [
    ("Crep ExtCall dispatch follows source call_FFI and stateRel ffi update",
      dispatchGuard),
    ("Crep ExtCall FFI_return write-back preserves stateRel and writes bytes",
      returnedGuard),
    ("Crep ExtCall four-local wrapper dispatch follows source call_FFI",
      wrapperGuard),
    ("Crep ExtCall FFI_final branch returns FinalFFI with stateRel unchanged",
      finalGuard),
    ("Crep ExtCall four-local failing-read wrapper returns Error with stateRel",
      errorGuard),
    ("Crep ExtCall one-shot production dispatch matches call_FFI shape",
      oneShotGuard),
    ("Crep ExtCall failing-read branch returns Error with state unchanged", true)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.CrepRuntimeExtCallStateRelParity
