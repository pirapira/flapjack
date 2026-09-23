import Flapjack.Pancake.Semantics.LoopSem

/-!
# Loop shared-memory (`sh_mem_op`) regression

Exercises the faithful 64-bit `loopShMemLoad`/`loopShMemStore`/`loopShMemOp`
ports against the direct HOL oracle
`scripts/hol-probes/loop_sem_sh_mem_op_probe.out`, whose rows are the byte
counts dispatched per operator.  The recording oracle below captures the
`SharedMem` configuration handed to `call_FFI`, so the byte-count row and the
result shapes (domain error, missing local, terminal FFI) are checked directly.
-/

namespace Flapjack.Test.LoopShMemParity

open Flapjack

abbrev Word := RiscV.Word 64

def recordingOracle (_name : FfiName) (state : List (List UInt8))
    (configuration _bytes : List UInt8) : FfiOracleResult (List (List UInt8)) :=
  .returned (configuration :: state) _bytes

def finalOracle (_name : FfiName) (_state : List (List UInt8))
    (_configuration _bytes : List UInt8) : FfiOracleResult (List (List UInt8)) :=
  .final .failed

def loadOracle (_name : FfiName) (state : List (List UInt8))
    (_configuration _bytes : List UInt8) : FfiOracleResult (List (List UInt8)) :=
  .returned state [7, 0, 0, 0, 0, 0, 0, 0]

def baseState (oracle : FfiOracle (List (List UInt8)))
    (oracleState : List (List UInt8)) (shared : Word → Bool) :
    LoopMachineState Word (List (List UInt8)) where
  locals := fun name => if name = 3 then some (.word 7) else none
  globals := fun _ => none
  memory := fun _ => none
  mdomain := fun _ => false
  shMdomain := shared
  clock := 10
  code := []
  be := false
  ffi := { oracle := oracle, state := oracleState, ioEvents := [] }
  baseAddr := 0
  topAddr := 0

def inDomain : Word → Bool := fun address => address == 0
def outOfDomain : Word → Bool := fun _ => false

def firstConfig : List (List UInt8) → List UInt8
  | [] => []
  | configuration :: _ => configuration

def opConfigs : List (List UInt8) :=
  [.load, .store, .load8, .store8, .load16, .store16, .load32, .store32].map
    (fun operator =>
      firstConfig (loopShMemOp (baseState recordingOracle [] inDomain)
        operator 3 0).2.ffi.state)

theorem opConfigs_eq :
    opConfigs = [[0], [0], [1], [1], [2], [2], [4], [4]] := rfl

def domainError : Bool :=
  match (loopShMemOp (baseState recordingOracle [] outOfDomain) .load8 3 0).1 with
  | some .error => true
  | _ => false

def missingStore : Bool :=
  match (loopShMemOp (baseState recordingOracle [] inDomain) .store8 5 0).1 with
  | some .error => true
  | _ => false

def finalResult : Bool :=
  match (loopShMemOp (baseState finalOracle [] inDomain) .load8 3 0).1 with
  | some (.finalFfi _) => true
  | _ => false

def loadValue : Bool :=
  match (loopShMemOp (baseState loadOracle [] inDomain) .load8 3 0).2.locals 3 with
  | some (.word value) => value == 7
  | _ => false

def missingLoadSets : Bool :=
  match (loopShMemOp (baseState loadOracle [] inDomain) .load8 4 0).2.locals 4 with
  | some (.word value) => value == 7
  | _ => false

#guard opConfigs == [[0], [0], [1], [1], [2], [2], [4], [4]]
#guard domainError
#guard missingStore
#guard finalResult
#guard loadValue
#guard missingLoadSets

/-! Width-generic `shMemLoadHOL`/`shMemStoreHOL`/`shMemOpHOL` checks.  At width
    64 the generic dispatch must agree with the RV64 instance.  At width 24 the
    HOL alignment is `LOG2 (24 DIV 8) = 1`, so address 5 aligns to 4 (not 3):
    the nonzero-width `load8` accepts the aligned in-domain address while the
    zero-width `load` checks the raw address 5 and fails. -/

abbrev Word24 := RiscV.Word 24

def baseState24 (shared : Word24 → Bool) :
    LoopMachineState Word24 (List (List UInt8)) where
  locals := fun name => if name = 3 then some (.word 7) else none
  globals := fun _ => none
  memory := fun _ => none
  mdomain := fun _ => false
  shMdomain := shared
  clock := 10
  code := []
  be := false
  ffi := { oracle := recordingOracle, state := [], ioEvents := [] }
  baseAddr := 0
  topAddr := 0

def domain24 : Word24 → Bool := fun address => address == 4

def genericConfigs : List (List UInt8) :=
  [.load, .store, .load8, .store8, .load16, .store16, .load32, .store32].map
    (fun operator =>
      firstConfig (shMemOpHOL (width := 64)
        (baseState recordingOracle [] inDomain) operator 3 0).2.ffi.state)

def width24Aligned : Bool :=
  match (shMemOpHOL (width := 24) (baseState24 domain24) .load8 3 5).1 with
  | none => true
  | _ => false

def width24Raw : Bool :=
  match (shMemOpHOL (width := 24) (baseState24 domain24) .load 3 5).1 with
  | some .error => true
  | _ => false

def width24Config : List UInt8 :=
  firstConfig (shMemOpHOL (width := 24) (baseState24 domain24) .load8 3 5).2.ffi.state

#guard genericConfigs == [[0], [0], [1], [1], [2], [2], [4], [4]]
#guard width24Aligned
#guard width24Raw
#guard width24Config == [1]

def runChecks : IO Bool := do
  let configsOk ←
    if opConfigs == [[0], [0], [1], [1], [2], [2], [4], [4]] then
      IO.println "PASS Loop sh_mem_op dispatches width 0/0/1/1/2/2/4/4"
      pure true
    else
      IO.println "FAIL Loop sh_mem_op width dispatch"
      pure false
  let shapeOk ←
    if domainError && missingStore && finalResult && loadValue && missingLoadSets then
      IO.println "PASS Loop sh_mem_load/store domain, missing-local, final and value cases"
      pure true
    else
      IO.println "FAIL Loop sh_mem_load/store cases"
      pure false
  let genericOk ←
    if genericConfigs == [[0], [0], [1], [1], [2], [2], [4], [4]] &&
        width24Aligned && width24Raw && width24Config == [1] then
      IO.println "PASS Loop width-generic sh_mem_op dispatch and width-24 HOL alignment"
      pure true
    else
      IO.println "FAIL Loop width-generic sh_mem_op"
      pure false
  pure (configsOk && shapeOk && genericOk)

end Flapjack.Test.LoopShMemParity
