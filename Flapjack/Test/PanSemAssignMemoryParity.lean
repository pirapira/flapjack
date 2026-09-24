import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Faithful source memory access for the panSem `Assign` equation

The source oracle is `scripts/hol-probes/pan_sem_assign_memory_probe.out`:

* `assign_mem_load_result=NONE`,
  `assign_mem_load_locals=SOME (ValWord 0x1122334455667788w)` — a whole-word
  `Load` source writes the loaded cell into the destination local;
* `assign_mem_domain_result=SOME Error`,
  `assign_mem_domain_locals=SOME (ValWord 3w)`,
  `assign_mem_domain_clock=5` — a `Load` whose address is outside `memaddrs`
  is the source-evaluation Error path with the state unchanged;
* `assign_mem_byte_le_locals=SOME (ValWord 0w)` and
  `assign_mem_byte_be_locals=SOME (ValWord 136w)` — `LoadByte` selects a
  different byte of the same cell under little- versus big-endian `be`.

These pin the state-owned RISC-V 64 source evaluator
`panSemEvaluateRiscV64CodeState`, which derives the memory domain and
endianness from the `PanSemState`, against the original HOL execution.  The
`Assign` equation used here is the access-threaded
`panSemEvaluateCodeStateWithFuel_assign_state_memory`.
-/

namespace Flapjack.Test.PanSemAssignMemoryParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Memory with `0x1122334455667788` at address 8 and zero elsewhere. -/
def nonzeroMemory : Word64 → Option (PanValue Word64) :=
  fun address => if address == 8 then some (.word 0x1122334455667788) else some (.word 0)

/-- Memory with the high byte `0x88` at address 8 and zero elsewhere. -/
def highByteMemory : Word64 → Option (PanValue Word64) :=
  fun address => if address == 8 then some (.word 0x8800000000000000) else some (.word 0)

/-- A source state exposing only address 8 and binding local `x` to `3`. -/
def assignMemoryState (memory : Word64 → Option (PanValue Word64)) (be : Bool)
    (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name => if name == "x" then some (.word 3) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := memory
    memaddrs := fun address => address == 8
    sharedMemaddrs := fun _ => false
    clock := clock
    be := be
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

/-- State-owned RISC-V 64 source evaluation of a single program. -/
def assignEvaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

def loadSource : Exp Word64 := .load .one (.const 8)

def loadMissSource : Exp Word64 := .load .one (.const 9)

def byteSource : Exp Word64 := .loadByte (.const 8)

/-- Does the destination local hold the expected word? -/
def isWordValue (expected : Word64) : Option (PanValue Word64) → Bool
  | some (.word value) => value == expected
  | _ => false

/-- Normal completion writing `expected` into local `x`. -/
def isNormalWith (expected : Word64) : Option (PanValueFfiClockResult Word64 Unit) → Bool
  | some (.control (.normal locals _ _ _), _) => isWordValue expected (locals "x")
  | _ => false

/-- Error completion keeping `expected` in local `x`. -/
def isErrorKeeping (expected : Word64) : Option (PanValueFfiClockResult Word64 Unit) → Bool
  | some (.control (.error locals _ _ _), _) => isWordValue expected (locals "x")
  | _ => false

/-- A `Load` source writes the loaded word. -/
def loadGuard : Bool :=
  isNormalWith 0x1122334455667788
    (assignEvaluate (assignMemoryState nonzeroMemory false 5)
      (.assign .local "x" loadSource))

/-- A `Load` outside the domain is the source-evaluation Error path. -/
def domainGuard : Bool :=
  isErrorKeeping 3
    (assignEvaluate (assignMemoryState nonzeroMemory false 5)
      (.assign .local "x" loadMissSource))

/-- Little-endian `LoadByte` selects the low byte. -/
def byteLEGuard : Bool :=
  isNormalWith 0
    (assignEvaluate (assignMemoryState highByteMemory false 5)
      (.assign .local "x" byteSource))

/-- Big-endian `LoadByte` selects the high byte. -/
def byteBEGuard : Bool :=
  isNormalWith 0x88
    (assignEvaluate (assignMemoryState highByteMemory true 5)
      (.assign .local "x" byteSource))

def assignMemoryGuard : Bool := loadGuard && domainGuard && byteLEGuard && byteBEGuard

#guard assignMemoryGuard

/-- The access-threaded `Assign` boundary equation over a memory-reading source
    at the state-derived access, matching the HOL oracle above. -/
def assignMemoryProbeState : PanSemState Word64 (FfiState Unit) :=
  assignMemoryState nonzeroMemory false 5

example :
    panSemEvaluateCodeStateWithFuel statefulTestContext statefulTestPrimitive
        statefulTestHandler panSemBitVec64BytesInWord (3 + 1) assignMemoryProbeState
        (.assign .local "x" loadSource) (memoryAccess := some (panValueMemoryAccessOfModel panSemBitVec64WordModel assignMemoryProbeState.memaddrs assignMemoryProbeState.sharedMemaddrs assignMemoryProbeState.be)) =
      match evalPanValueExp assignMemoryProbeState.structs assignMemoryProbeState.locals
          assignMemoryProbeState.globals assignMemoryProbeState.memory
          assignMemoryProbeState.baseAddress assignMemoryProbeState.topAddress
          panSemBitVec64BytesInWord loadSource (memoryAccess := some (panValueMemoryAccessOfModel panSemBitVec64WordModel assignMemoryProbeState.memaddrs assignMemoryProbeState.sharedMemaddrs assignMemoryProbeState.be)) with
      | some evaluated =>
          if panValueAssignmentValid assignMemoryProbeState.structs
              assignMemoryProbeState.locals assignMemoryProbeState.globals .local "x"
              evaluated then
            some ((.control (.normal (updatePanValueMap assignMemoryProbeState.locals "x"
                evaluated) assignMemoryProbeState.globals assignMemoryProbeState.memory
                assignMemoryProbeState.ffi), assignMemoryProbeState.clock))
          else
            some ((.control (.error assignMemoryProbeState.locals
              assignMemoryProbeState.globals assignMemoryProbeState.memory
              assignMemoryProbeState.ffi), assignMemoryProbeState.clock))
      | none =>
          some ((.control (.error assignMemoryProbeState.locals assignMemoryProbeState.globals
            assignMemoryProbeState.memory assignMemoryProbeState.ffi),
            assignMemoryProbeState.clock)) := by
  rw [panSemEvaluateCodeStateWithFuel_assign_state_memory statefulTestContext
    statefulTestPrimitive statefulTestHandler panSemBitVec64WordModel
    panSemBitVec64BytesInWord 3 assignMemoryProbeState .local "x" loadSource]
  cases h : evalPanValueExp assignMemoryProbeState.structs assignMemoryProbeState.locals
      assignMemoryProbeState.globals assignMemoryProbeState.memory
      assignMemoryProbeState.baseAddress assignMemoryProbeState.topAddress
      panSemBitVec64BytesInWord loadSource
      (memoryAccess := some (panValueMemoryAccessOfModel panSemBitVec64WordModel
        assignMemoryProbeState.memaddrs assignMemoryProbeState.sharedMemaddrs
        assignMemoryProbeState.be)) with
  | none => rfl
  | some evaluated => rfl

def runChecks : IO Bool := do
  let mut ok := true
  if loadGuard then
    IO.println "PASS panSem Assign memory source writes the loaded word"
  else
    IO.println "FAIL panSem Assign memory source writes the loaded word"
    ok := false
  if domainGuard then
    IO.println "PASS panSem Assign memory source outside domain rejected with Error and unchanged state"
  else
    IO.println "FAIL panSem Assign memory source outside domain rejected with Error and unchanged state"
    ok := false
  if byteLEGuard then
    IO.println "PASS panSem Assign little-endian byte source selects the low byte"
  else
    IO.println "FAIL panSem Assign little-endian byte source selects the low byte"
    ok := false
  if byteBEGuard then
    IO.println "PASS panSem Assign big-endian byte source selects the high byte"
  else
    IO.println "FAIL panSem Assign big-endian byte source selects the high byte"
    ok := false
  pure ok

end Flapjack.Test.PanSemAssignMemoryParity
