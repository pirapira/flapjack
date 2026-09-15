import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.StackAlloc.Machine

namespace Flapjack

open RiscV

/-! Direct Cake oracle guard for the six-instruction RISC-V carry expansion.
    This count is consumed by the Lab linker when computing later labels. -/
#guard
  RiscV.labLineInstructionCount
      (.asm (.word (.arith (.cakeAddCarry 10 10 16 1))) [] 0 :
        LabLine (RiscV.Word 64)) = 6

#guard
  RiscV.labSectionInstructionCount
      ({ name := 17,
         lines := [.asm (.word (.arith (.cakeAddCarry 10 10 16 1))) [] 0] } :
        LabSection (RiscV.Word 64)) = 6

def pipelineDiagnosticsConfig : WordStackConfig :=
  { locations := [(0, .register 5), (1, .register 6),
      (2, .register 7), (3, .register 8)]
    scratch := 31
    stackBase := 10 }

def diagnosticCompiledMain : CompiledFunction Nat :=
  { name := "main", params := [], body := .skip, returnShape := .one }

example :
    pipelineFunctionNameAtLabel 1 [diagnosticCompiledMain] 1 = some "main" := by
  rfl

example :
    sourceRiscVImageErrorOfLowering 1 [diagnosticCompiledMain]
        (.allocationFailure 1) =
      .loweringInFunction "main" (.allocationFailure 1) := by
  rfl

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(17, [], (.alloc 0 ([], []) : WordProg (RiscV.Word 64)))] =
        .error { sectionId := 17, path := [], feature := .alloc } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(23, [], ((.seq .skip (.storeConsts 0 1 2 3 [])) :
        WordProg (RiscV.Word 64)))] =
        .error { sectionId := 23, path := [1], feature := .storeConsts } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨17, [.labAsm (.heapAlloc 3) [] 0]⟩] =
        .error { sectionId := 17, position := 0, feature := .heapAlloc } := by
  rfl

/-! The linked checked boundary retains the same section/position diagnostic;
the historical linked API would collapse this failure to `none`. -/
example :
    RiscV.compileLabProgramLinkedChecked (width := 64) { services := [] }
      [⟨17, [.labAsm (.heapAlloc 3) [] 0]⟩] =
        .error { sectionId := 17, position := 0, feature := .heapAlloc } := by
  rfl

/-! The halt-aware linker used by the SimpleGC runtime preserves the same
    section/position diagnostic instead of collapsing to `artifactFailure`. -/
example :
    RiscV.compileLabProgramLinkedWithHaltChecked (width := 64) { services := [] }
      [⟨17, [.labAsm (.heapAlloc 3) [] 0]⟩] =
        .error { sectionId := 17, position := 0, feature := .heapAlloc } := by
  rfl

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨29, [.asm (.word (.arith (.longDiv 0 3 3 0 6))) [] 0]⟩] =
        .error { sectionId := 29, position := 0, feature := .longDiv } := by
  rfl

/-! CakeML's RISC-V target rejects a direct `LongDiv` instruction
    (`riscv_targetScript.sml:143`).  Software lowering must therefore happen
    through the `LongDiv_code`/`LongDiv1_code` helper path rather than by
    teaching the direct instruction selector a new encoding. -/
example :
    RiscV.wordArithToInstructions (width := 64)
      (.longDiv 0 3 3 0 6) = none := by
  rfl

/-! The direct selector rejection is distinct from the source compiler path:
    the normalized source LongDiv is replaced by the linked CakeML software
    helper sections before Lab lowering. -/
def longDivSourceEntryRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

#guard
  (RiscV.compileStackProgramNatToRiscVChecked (width := 64) { services := [] }
    longDivSourceEntryRemoveConfig 29 0
    (.inst (.arith (.longDiv 0 3 3 0 6)) : StackProg Nat)).isOk

def longDivRuntimeSemanticConfig : StackRemoveConfig :=
  { longDivSourceEntryRemoveConfig with bytesInWord := 1 }

def longDivRuntimeSemanticState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 3 then BitVec.ofNat 8 1
      else if register = 0 then BitVec.ofNat 8 3
      else if register = 6 then BitVec.ofNat 8 2
      else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def longDivRuntimeSemanticResult :
    Option (StackMachineControl 8) := do
  let helpers ← RiscV.cakeLongDivRuntimeSections longDivRuntimeSemanticConfig
  RiscV.evalStackSectionsFuel 10000
    (helpers ++ [(29, RiscV.cakeLongDivStackAdapter)]) 29
    longDivRuntimeSemanticState

#guard
  match longDivRuntimeSemanticResult with
  | some (.normal state) =>
      state.registers 0 = BitVec.ofNat 8 129 &&
        state.registers 3 = BitVec.ofNat 8 1
  | _ => false

/-! The HOL fixture `scripts/hol-probes/longdiv_code_probe.out` contains the
    two source-level CakeML AddCarry operations
    `AddCarry 10 10 16 1` and `AddCarry 12 12 14 1`.  Check the exact
    four-register operations in the source-shaped helper, including order,
    rather than only checking its end-to-end result. -/
def cakeAddCarryOps : WordProg Nat → List (Nat × Nat × Nat × Nat)
  | .inst (.arith (.cakeAddCarry destination sourceLeft sourceRight carry)) =>
      [(destination, sourceLeft, sourceRight, carry)]
  | .seq first second => cakeAddCarryOps first ++ cakeAddCarryOps second
  | .ite _ _ _ thenBranch elseBranch =>
      cakeAddCarryOps thenBranch ++ cakeAddCarryOps elseBranch
  | .loop _ body _ => cakeAddCarryOps body
  | .mustTerminate body => cakeAddCarryOps body
  | .call returns _ _ handler =>
      (match returns with
      | some (_, _, body, _, _) => cakeAddCarryOps body
      | none => []) ++
      (match handler with
      | some (_, body, _, _) => cakeAddCarryOps body
      | none => [])
  | _ => []

#guard
  cakeAddCarryOps (RiscV.cakeLongDiv1Code 8) =
    [(10, 10, 16, 1), (12, 12, 14, 1)]

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨19, [.asm (.const 1 7) [] 0]⟩] =
        .ok [.ori 1 0 (BitVec.ofNat 64 7)] := by
  rfl

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
        .ok [.jal 0 (BitVec.ofNat 64 4),
          .ori 1 0 (BitVec.ofNat 64 7)] := by
  rfl

def checkedPipelineDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

def checkedPipelineRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

#guard
    (compileFlapjackRiscVViaStackChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      checkedPipelineRemoveConfig checkedPipelineDeclarations).isOk

#guard
    (compileFlapjackRiscVViaStackBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      checkedPipelineRemoveConfig checkedPipelineDeclarations).isOk

#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok artifact => artifact.bytes.length > 0
    | .error _ => false

/-! The public source entrypoint must accept calls as well as closed returns. -/
#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main"
      "fun 1 id(1 x) { return x; }\nfun 1 main() { var 1 answer = id(41); return answer; }" with
    | .ok artifact => artifact.bytes.length > 0
    | .error _ => false

/-! Cake-compatible structured store addresses must survive the source-facing
    pipeline as well as the parser/static checker. -/
#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main"
      "fun 1 main() { var {1} x = <1>; st x.0, x.0; return 1; }" with
    | .ok artifact => artifact.bytes.length > 0
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "var 1 global = 7;\nfun 1 main() { return global; }" with
    | .ok image => image.sections.length > 0 && image.bitmaps.data.length > 0
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "var {1} global = <7>;\nfun 1 main() { return global.0; }" with
    | .ok image => image.sections.length > 0 && image.bitmaps.data.length > 0
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() {" with
    | .error (.parse _) => true
    | _ => false

#guard
    match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok image => image.sections.length > 0 &&
        image.sections.all (fun entry => entry.bytes.length % 4 == 0)
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "missing" "fun main() { return 7; }" with
    | .error .entryNotFound => true
    | _ => false

#guard
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok image => image.bitmaps.data.length > 0 && image.sections.length > 0 &&
        image.sections.all (fun entry => entry.bytes.length % 4 == 0)
    | .error _ => false

/-! Original Pancake also accepts a computed address for an ordinary local
    store.  Keep this source-facing regression separate from the structured
    address case above: the address is a nested expression and the value is a
    scalar local. -/
def nestedLocalStoreSource : String :=
  "fun 1 main() { var 1 x = 7; st 1000 + 12, x; return x; }"

#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" nestedLocalStoreSource with
    | .ok artifact => artifact.bytes.length > 0 && artifact.bytes.length % 4 == 0
    | .error _ => false

def nestedLocalStoreBytesAccepted : Bool :=
  match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" nestedLocalStoreSource with
  | .ok artifact => artifact.bytes.length > 0 && artifact.bytes.length % 4 == 0
  | .error _ => false

end Flapjack
