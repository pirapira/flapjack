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

/-! The Cake software path prepends the two code-table helpers before the
    raise stub and user section.  Keep that linked ordering explicit: Lab
    relocation and helper calls depend on these labels, while direct RISC-V
    LongDiv encoding remains rejected above. -/
def longDivLinkedSectionOrder : Bool :=
  match RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscVCakeChecked
      (width := 8) { services := [] } longDivRuntimeSemanticConfig 29 0
      [(29, (.inst (.arith (.longDiv 0 3 3 0 6)) : StackProg Nat))] with
  | .ok sections => sections.map (fun entry => entry.1) ==
      [RiscV.cakeLongDiv1Location, RiscV.cakeLongDivLocation,
       stackRaiseStubLocation, 29]
  | .error _ => false

#guard longDivLinkedSectionOrder

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

/-! The checked-in HOL `longdiv_code_probe.out` also fixes the helper call
    ABI, not just the AddCarry instructions.  In particular, LongDiv_code
    passes its seven source words in the order `[0;11;6;10;10;4;2]`, while
    LongDiv1_code uses the six-word recursive ABI `[0;2;4;6;8;10;12]`.
    Keep these call shapes explicit so a future entry-slot or argument-order
    change cannot silently invalidate the source-shaped runtime. -/
def wordCallShapes : WordProg Nat → List (Option Nat × List Nat)
  | .call _ target arguments _ => [(target, arguments)]
  | .seq first second => wordCallShapes first ++ wordCallShapes second
  | .ite _ _ _ thenBranch elseBranch =>
      wordCallShapes thenBranch ++ wordCallShapes elseBranch
  | .loop _ body _ => wordCallShapes body
  | .mustTerminate body => wordCallShapes body
  | _ => []

def longDivHelperCallAbiExact : Bool :=
  wordCallShapes (RiscV.cakeLongDivCode 64) ==
      [(some RiscV.cakeLongDiv1Location, [0, 11, 6, 10, 10, 4, 2])] &&
    wordCallShapes (RiscV.cakeLongDiv1Code 64) ==
      [(some RiscV.cakeLongDiv1Location, [0, 2, 4, 6, 8, 10, 12]),
       (some RiscV.cakeLongDiv1Location, [0, 2, 4, 6, 8, 10, 12]),
       (some RiscV.cakeLongDiv1Location, [0, 2, 4, 6, 8, 10, 12])]

#guard longDivHelperCallAbiExact

#guard
  cakeAddCarryOps (RiscV.cakeLongDiv1Code 8) =
    [(10, 10, 16, 1), (12, 12, 14, 1)]

/-! Pin the complete width-8 helper shape from
    `scripts/hol-probes/longdiv_code_probe.out`, not only its calls and
    AddCarry leaves.  This is the Cake `LongDiv1_code` software path selected
    when `has_longdiv = F`; the direct RISC-V LongDiv selector remains
    intentionally rejecting the hardware instruction above. -/
def cakeLongDiv1Code8Oracle : WordProg Nat :=
  .ite .test 2 (.reg 2)
    (.seq (.set (.temp 28) (.var 10)) (.return 0 [8]))
    (RiscV.cakeWordSeq [
      .assign 6 (.op .or [
        .shift .lsr (.var 6) (.const 1),
        .shift .lsl (.var 4) (.const 7)]),
      .assign 4 (.shift .lsr (.var 4) (.const 1)),
      .assign 8 (.shift .lsl (.var 8) (.const 1)),
      .assign 2 (.op .sub [.var 2, .const 1]),
      .ite .lower 12 (.reg 4) RiscV.cakeLongDiv1Call .skip,
      .ite .equal 12 (.reg 4)
        (.ite .lower 10 (.reg 6) RiscV.cakeLongDiv1Call .skip)
        .skip,
      .assign 8 (.op .add [.var 8, .const 1]),
      .assign 16 (.op .xor [.var 6, .const 255]),
      .assign 14 (.op .xor [.var 4, .const 255]),
      .assign 1 (.const 1),
      .inst (.arith (.cakeAddCarry 10 10 16 1)),
      .inst (.arith (.cakeAddCarry 12 12 14 1)),
      RiscV.cakeLongDiv1Call])

example : RiscV.cakeLongDiv1Code 8 = cakeLongDiv1Code8Oracle := by
  rfl

def cakeLongDivCode8Oracle : WordProg Nat :=
  RiscV.cakeWordSeq [
    .assign 10 (.const 0),
    .assign 11 (.const 8),
    .call none (some RiscV.cakeLongDiv1Location)
      [0, 11, 6, 10, 10, 4, 2] none]

example : RiscV.cakeLongDivCode 8 = cakeLongDivCode8Oracle := by
  rfl

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

/-! GH #1157 (`Normalize or explain mode-specific section IDs in lowering
    errors`): the section id recorded in a lowering error is a crepe-local
    label, not a stable function identity.  `--hex` numbers crepe sections
    from 1 while the default runtime-image mode numbers them from
    `stackFunctionFirstLabel`, so the equal failing function shows up as
    different section ids.  These guards pin the presentation-layer regression
    without changing the internal Cake-compatible labels. -/
def diagnosticCompiledFunctions : List (CompiledFunction Nat) :=
  [ { name := "helper", params := [], body := .skip, returnShape := .one },
    diagnosticCompiledMain ]

def hexModeLoweringError : SourceRiscVCompileError :=
  sourceRiscVCompileErrorOfLowering 1 diagnosticCompiledFunctions
    (.allocationFailure 2)

def runtimeModeLoweringError : SourceRiscVImageError :=
  sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
    diagnosticCompiledFunctions (.allocationFailure 4)

def compileErrorFunction : SourceRiscVCompileError → Option FunName
  | .loweringInFunction functionName _ => some functionName
  | _ => none

def imageErrorFunction : SourceRiscVImageError → Option FunName
  | .loweringInFunction functionName _ => some functionName
  | _ => none

example :
    hexModeLoweringError = .loweringInFunction "main" (.allocationFailure 2) := by
  rfl

example :
    runtimeModeLoweringError = .loweringInFunction "main" (.allocationFailure 4) := by
  rfl

#guard stackFunctionFirstLabel = 3

/-! The same failing function keeps a single stable identity while the
    mode-local section ids differ by two. -/
#guard compileErrorFunction hexModeLoweringError = some "main"
#guard imageErrorFunction runtimeModeLoweringError = some "main"

#guard
  sourceRiscVCompileErrorDescription hexModeLoweringError =
    "in function 'main': register allocation failed in mode-local section 2"

#guard
  sourceRiscVImageErrorDescription runtimeModeLoweringError =
    "in function 'main': register allocation failed in mode-local section 4"

/-! An unresolved section id still reports as mode-local rather than leaking a
    bare number as if it were stable. -/
#guard
  sourceRiscVImageErrorDescription
      (sourceRiscVImageErrorOfLowering 1 [diagnosticCompiledMain]
        (.allocationFailure 5)) =
    "register allocation failed in mode-local section 5"

#guard
  sourceRiscVCompileErrorDescription .entryNotFound =
    "no entry point named 'main'"

end Flapjack
