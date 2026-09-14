import Flapjack.PanEvaluate
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for Pancake `evaluate_def`

The source oracle is `scripts/hol-probes/pan_sem_e2e_probe.out`, generated
from `panSemScript.sml:556-736`.  Its `return_41`, `return_mul_42`, and
`return_if_13` observations are direct HOL evaluations of
`FST (panSem$evaluate ...)`; the call, memory, and FFI fixtures use the same
source boundary.  These checks exercise the source-shaped wrapper on a
constant return, an intermediate clocked sequence, a zero-clock timeout, and
a function call with argument transfer and return-shape contracts.

The fixed-width memory oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_load_probe.out`, generated from
`panSemScript.sml:247-265` and the referenced `mem_load_byte_def` /
`mem_load_32_def` equations. It pins aligned success, domain failure,
little-endian reconstruction, and alignment failure.

The explicit-memory store oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_store_probe.out`, generated from
`panSemScript.sml:300-390` and `evaluate_def` at :589-608. It checks ordinary
word stores, `Store32`, and `StoreByte` through the source memory domain,
including domain/alignment failures and preservation of the other state
components.
-/

namespace Flapjack.Test.PanEvaluateParity

open Flapjack
open Flapjack.RiscV

def emptyPanState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { structs := []
    functions := []
    locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8 }

def evaluateSkip :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.skip : Prog (Word 64))

def evaluateReturn41 :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.return (.const (BitVec.ofNat 64 41)) : Prog (Word 64))

def evaluateSequence :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 1)
    ((.seq .tick (.return (.const (BitVec.ofNat 64 13)))) : Prog (Word 64))

def evaluateTickAtZero :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 0) (.tick : Prog (Word 64))

def idFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def idContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("id", .one)] [] [("id", [("x", .one)])]

def evaluateCall :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    ({ emptyPanState 10 with
        functions := idFunctions
        contracts := some idContracts }
      : PanSemEvaluateState (Word 64) Unit)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog (Word 64))

/-! The fixed-width branches must go through the explicit source memory model.
    This is the stateful evaluator path corresponding to
    `panSemScript.sml:247-265`, not the legacy whole-cell fallback. -/
def fixedLoadDomain : PanMemoryDomain (Word 64) :=
  fun address => address == BitVec.ofNat 64 8

def fixedLoadMemory : Word 64 → Option (PanValue (Word 64)) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x0807060504030201))
    else none

def fixedLoadAccess : PanValueMemoryAccess (Word 64) :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel fixedLoadDomain

def fixedLoadState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { emptyPanState clock with
      memory := fixedLoadMemory
      memoryAccess := some fixedLoadAccess }

def fixedStoreLocals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "kept" then some (.word (BitVec.ofNat 64 55)) else none

def fixedStoreGlobals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "keptGlobal" then some (.word (BitVec.ofNat 64 66)) else none

def fixedStoreState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { fixedLoadState clock with
      locals := fixedStoreLocals
      globals := fixedStoreGlobals }

def evaluateFixedByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 9))) : Prog (Word 64))

def evaluateFixedWord32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

def evaluateFixedByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 16))) : Prog (Word 64))

def evaluateFixedStore :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStoreDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStore32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStore32Unaligned :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStoreByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def evaluateFixedStoreByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def isWord (expected : Nat) : PanValue (Word 64) → Bool
  | .word value => value == BitVec.ofNat 64 expected
  | _ => false

def observeSkip : Bool :=
  match evaluateSkip with
  | some (.control (.normal locals _ _ _), 4) => locals "x" = none
  | _ => false

def observeReturn41 : Bool :=
  match evaluateReturn41 with
  | some (.control (.returned locals _ _ _ [value]), 4) =>
      locals "x" = none && isWord 41 value
  | _ => false

def observeSequence : Bool :=
  match evaluateSequence with
  | some (.control (.returned _ _ _ _ [value]), 0) => isWord 13 value
  | _ => false

def observeTickAtZero : Bool :=
  match evaluateTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

def observeCall : Bool :=
  match evaluateCall with
  | some (.control (.returned locals _ _ _ [value]), 9) =>
      locals "x" = none && isWord 7 value
  | _ => false

def observeFixedLoads : Bool :=
  match evaluateFixedByte, evaluateFixedWord32 with
  | some (.control (.returned _ _ _ _ [(.word byte)]), 4),
      some (.control (.returned _ _ _ _ [(.word word32)]), 4) =>
      byte == BitVec.ofNat 64 2 && word32 == BitVec.ofNat 64 0x04030201
  | _, _ => false

def observeFixedLoadDomainFailure : Bool :=
  evaluateFixedByteDomainFailure.isNone

def isWordOption (expected : Nat) : Option (PanValue (Word 64)) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

def isNoneOption : Option (PanValue (Word 64)) → Bool
  | none => true
  | _ => false

def observeFixedStore : Bool :=
  match evaluateFixedStore with
  | some (.control (.normal locals globals memory ffi), 4) =>
      isWordOption 55 (locals "kept") &&
      isWordOption 66 (globals "keptGlobal") &&
      isWordOption 0x1122334455667788 (memory (BitVec.ofNat 64 8)) &&
      isNoneOption (memory (BitVec.ofNat 64 16)) &&
      decide (ffi.ioEvents = statefulTestFfiState.ioEvents)
  | _ => false

def observeFixedStore32 : Bool :=
  match evaluateFixedStore32 with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x0807060511223344 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreByte : Bool :=
  match evaluateFixedStoreByte with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x080706050403aa01 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreFailures : Bool :=
  evaluateFixedStoreDomainFailure.isNone &&
    evaluateFixedStore32Unaligned.isNone &&
    evaluateFixedStoreByteDomainFailure.isNone

#guard observeSkip
#guard observeReturn41
#guard observeSequence
#guard observeTickAtZero
#guard observeCall
#guard observeFixedLoads
#guard observeFixedLoadDomainFailure
#guard observeFixedStore
#guard observeFixedStore32
#guard observeFixedStoreByte
#guard observeFixedStoreFailures

def runChecks : IO Bool := do
  if observeSkip then IO.println "PASS evaluate skip" else IO.println "FAIL evaluate skip"
  if observeReturn41 then IO.println "PASS evaluate return_41" else IO.println "FAIL evaluate return_41"
  if observeSequence then IO.println "PASS evaluate sequence" else IO.println "FAIL evaluate sequence"
  if observeTickAtZero then IO.println "PASS evaluate timeout" else IO.println "FAIL evaluate timeout"
  if observeCall then IO.println "PASS evaluate call_id_7" else IO.println "FAIL evaluate call_id_7"
  if observeFixedLoads then IO.println "PASS evaluate fixed-width loads" else
    IO.println "FAIL evaluate fixed-width loads"
  if observeFixedLoadDomainFailure then IO.println "PASS evaluate fixed-width domain failure" else
    IO.println "FAIL evaluate fixed-width domain failure"
  if observeFixedStore then IO.println "PASS evaluate explicit word store" else
    IO.println "FAIL evaluate explicit word store"
  if observeFixedStore32 then IO.println "PASS evaluate explicit Store32" else
    IO.println "FAIL evaluate explicit Store32"
  if observeFixedStoreByte then IO.println "PASS evaluate explicit StoreByte" else
    IO.println "FAIL evaluate explicit StoreByte"
  if observeFixedStoreFailures then IO.println "PASS evaluate explicit store failures" else
    IO.println "FAIL evaluate explicit store failures"
  pure (observeSkip && observeReturn41 && observeSequence && observeTickAtZero && observeCall &&
    observeFixedLoads && observeFixedLoadDomainFailure && observeFixedStore &&
    observeFixedStore32 && observeFixedStoreByte && observeFixedStoreFailures)

end Flapjack.Test.PanEvaluateParity
