import Flapjack.Pipeline
import Flapjack.Pancake.LoopToWord
import Flapjack.Parser
import Flapjack.Parser.ParseTopDecsByteRanged
import Flapjack.RiscV.Encoding
import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.WordInstSelect
import Flapjack.RiscV.WordSimp
import Flapjack.RiscV.WordUnreach

/-!
# Checked pipeline Word-to-Stack diagnostics

The historical pipeline boundary returns `Option`, which is convenient for
existing executable artifacts but loses the reason a function could not be
lowered.  This wrapper retains the function section label and the checked
Word diagnostic while leaving that API unchanged.
-/

namespace Flapjack.RiscV

structure PipelineWordLoweringError where
  sectionId : Nat
  path : List Nat
  feature : WordUnsupportedFeature
  deriving DecidableEq, Repr

/-- Cake's `stack_var_count` for one lowered function
(`word_to_stackScript.sml:586-593`).

`compile_prog` takes `max_var prog DIV 2 + 1 - reg_count` of the program it is
about to lower, which is the output of `word_alloc`;
`cakeAllocateWordFunctionAfterDead` has already computed exactly that and
returns it as `allocation.nextSpill`.  The original `compile_prog` separately
accounts for the function's formal stack-argument area, not nested call
argument lists, so no additional call-arity term belongs here.

`stack_arg_count = arg_count - reg_count` uses the same `reg_count`
`word_to_stack$compile` computes once for the whole program
(`word_to_stackScript.sml:605`): `asm_conf.reg_count - (5 + LENGTH
asm_conf.avoid_regs)`, which for RISC-V is `cakeRiscVRegisterCount`.  A
literal `12` here made every function with twelve or more word parameters
reserve a frame Cake does not: `fun 1 f({1,1,1,1,1,1} a, {1,1,1,1,1,1} b)
{ return 0; }` came out as an `addi sp`, a stack-overflow check and a
matching `addi` around a body that is one `ori`.  `Pipeline.lean` already
used `cakeRiscVRegisterCount` for the same term. -/
def cakeWordFrameSlots [NeZero width] (allocation : WordSpillState)
    (wordParameters : List Nat)
    (_renamedProgram : WordProg (RiscV.Word width)) : Nat :=
  let cakeFrameSlots := allocation.nextSpill
  max cakeFrameSlots
    (wordParameters.length - RiscV.CakeRegAlloc.cakeRiscVRegisterCount)

def pipelineWordFunctionsToStackChecked [NeZero width] :
    List (Nat × List Nat × WordProg (Word width)) →
      Except PipelineWordLoweringError
        (List (Nat × List Nat × StackProg Nat))
  | [] => .ok []
  | (label, parameters, body) :: functions =>
      let config := { wordStackIdentityConfig body with
        sectionId := label
        handlerLabel := label }
      match wordToStackProgWordChecked config body with
      | .error error =>
          .error { sectionId := label, path := error.path, feature := error.feature }
      | .ok stackBody =>
          match pipelineWordFunctionsToStackChecked functions with
          | .error error => .error error
          | .ok rest => .ok ((label, parameters, stackBody) :: rest)

end Flapjack.RiscV

namespace Flapjack.RiscV

/-! In Cake's source-shaped FFI path, `word_to_stack` passes the abstract
    argument registers directly to `FFI`; `riscv_names` performs the final
    hardware-register naming later.  The general port path materializes those
    arguments into 10--13 first.  The source runtime path removes exactly that
    materialization before the Lab register map, while retaining all other
    moves (in particular stack-resident arguments). -/
def stackCakeFfiAbiTail : StackProg Nat → Option (StackProg Nat)
  | .seq (.arith .or configuration configurationSource configurationSourceRight)
      (.seq (.arith .or configurationLength configurationLengthSource configurationLengthSourceRight)
        (.seq (.arith .or array arraySource arraySourceRight)
          (.seq (.arith .or arrayLength arrayLengthSource arrayLengthSourceRight)
            (.ffi function 10 11 12 13 returnAddress)))) =>
      if configuration = 10 && configurationLength = 11 &&
          array = 12 && arrayLength = 13 &&
          configurationSource = configurationSourceRight &&
          configurationLengthSource = configurationLengthSourceRight &&
          arraySource = arraySourceRight &&
          arrayLengthSource = arrayLengthSourceRight then
        some (.ffi function configurationSource configurationLengthSource
          arraySource arrayLengthSource returnAddress)
      else none
  | _ => none

def stackNormalizeCakeFfi : StackProg Nat → StackProg Nat
  | .seq first second =>
      match stackCakeFfiAbiTail (.seq first second) with
      | some normalized => normalized
      | none => .seq (stackNormalizeCakeFfi first) (stackNormalizeCakeFfi second)
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.RiscV

namespace Flapjack

inductive PipelineRiscVLoweringError where
  | wordToStack (error : RiscV.PipelineWordLoweringError)
  | allocationFailure (sectionId : Nat)
  | wordToStackFailure (sectionId : Nat) (path : List Nat)
  | labToRiscV (error : RiscV.LabLoweringError)
  | stackToRiscV
  deriving DecidableEq, Repr

/-! Cake renames every Lab register through `riscv_names`
    (`riscv_stack_conf.reg_names` in
    `cakeml/compiler/backend/riscv/riscv_configScript.sml`), and
    `word_to_stack` numbers Lab registers by the physical half of the Word
    variable, so the hardware register of an abstract Word name `n` is
    `riscv_names (n / 2)`.  The map is the identity outside its recorded
    entries, so translating every even name (the ABI argument names and the
    ordinary names introduced by full SSA alike) is faithful; odd names are
    not used as fixed sources. -/
def wordRiscVAbiSourceRegister (source : Nat) : Nat :=
  if source % 2 = 0 then RiscV.riscvRegisterName (source / 2) else source

def wordRiscVFixedSourceLocations : List Nat → NatInfoMap WordLocation
  | [] => []
  | source :: sources =>
      (source, .register (wordRiscVAbiSourceRegister source)) ::
        wordRiscVFixedSourceLocations sources

def wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesRiscV [OfNat α 0]
    (currentFunction : Nat) (parameters : List Nat) (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  RiscV.CakeRegAlloc.cakeAllocateWordFunction parameters program
    currentFunction RiscV.CakeRegAlloc.cakeRiscVRegisterCount

/-! Checked counterpart of the full-SSA spill pipeline.  The historical
`Option` function intentionally keeps the old API, but it loses which Word
section failed when allocation or location-aware Word-to-Stack lowering
returns `none`.  Keep the same pass ordering and identify the first failing
section for source-facing diagnostics. -/
def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Except PipelineRiscVLoweringError
        (List (Nat × List Nat × StackProg Nat))
  | [] => .ok []
  | (label, parameters, body) :: functions =>
      let wordParameters := wordSsaAbiParameters parameters.length
      /- Keep the selected program intact until full SSA, matching Cake's
         `word_to_word` order.  `word_unreach` runs after SSA and cleanup;
         doing it here changes the fresh-name bound used by SSA. -/
      let unallocatedBody :=
        RiscV.wordInstSelectProgramFrom
          (RiscV.wordToWordPreSsa
            (RiscV.wordFlattenProgramFrom
              (LoopToWord.loopToWordCompFunc label parameters body)))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          /- Cake reserves allocator spills and the function's formal
             arguments outside the physical ABI window. -/
          let frameSlots := max allocation.nextSpill
            (wordParameters.length - RiscV.CakeRegAlloc.cakeRiscVRegisterCount)
          -- x23 stays clear of every Cake colour (x29 is colour 12 and can
          -- hold a call argument), so the parallel-move source check never trips.
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := 23
              abiBase := 1
              abiStride := 1
              abiFrameSlots := frameSlots
              sectionId := label
              handlerLabel := label }
          let lower :=
            if frameSlots = 0 then
              RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves config
                renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots (some 1)
                (RiscV.wordStackInitialBitmaps false) renamedProgram
            else
              RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves config
                renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots (some 1)
                (RiscV.wordStackInitialBitmaps false) renamedProgram
          match lower with
          | none =>
              let path := (RiscV.wordProgFirstExpressionLoweringFailure config
                (RiscV.wordProgToNat renamedProgram)).getD []
              .error (.wordToStackFailure label path)
          | some (stackBody, _) =>
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked functions with
              | .error error => .error error
              | .ok rest => .ok ((label, wordParameters, stackBody) :: rest)

/-! Checked bitmap-threaded sibling of the full-SSA spill pipeline.  The
    bitmap state is part of the runtime artifact, so keep it synchronized with
    the same first-failing section diagnostics used by the byte pipeline.

    The lowering only consults `length` while it is compiling a function: the
    bitmap `data` field is used solely to append newly emitted chunks.  Keeping
    the already-emitted global table in that field made every append copy the
    whole table, which became quadratic on the large guest.  The auxiliary
    worker therefore starts each function with an empty local data list but
    the absolute bitmap length, and carries the local chunks separately.  The
    wrapper materializes the same ordered table once at the end. -/
def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsCheckedAux
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState)
    (chunks : List (List Nat)) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Except PipelineRiscVLoweringError
        (List (Nat × List Nat × StackProg Nat) ×
          RiscV.WordStackBitmapState × List (List Nat))
  | [] => .ok ([], bitmaps, chunks)
  | (label, parameters, body) :: functions =>
      let wordParameters := wordSsaAbiParameters parameters.length
      let unallocatedBody :=
          RiscV.wordInstSelectProgramFrom
            (RiscV.wordToWordPreSsa
              (RiscV.wordFlattenProgramFrom
                (LoopToWord.loopToWordCompFunc label parameters body)))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          let frameSlots :=
            RiscV.cakeWordFrameSlots allocation wordParameters renamedProgram
          -- x23 stays clear of every Cake colour (x29 is colour 12 and can
          -- hold a call argument), so the parallel-move source check never trips.
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := 23
              abiBase := 1
              abiStride := 1
              abiFrameSlots := frameSlots
              sectionId := label
              handlerLabel := label }
          let localState : RiscV.WordStackBitmapState :=
            { data := [], length := bitmaps.length }
          let lower :=
            if frameSlots = 0 then
              RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves config
                renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots
                (some 1) localState renamedProgram
            else
              RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves config
                renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots
                (some 1) localState renamedProgram
          match lower with
          | none =>
              let path := (RiscV.wordProgFirstExpressionLoweringFailure config
                (RiscV.wordProgToNat renamedProgram)).getD []
              .error (.wordToStackFailure label path)
          | some (stackBody, nextBitmaps) =>
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsCheckedAux
                  nextBitmaps (nextBitmaps.data :: chunks) functions with
              | .error error => .error error
              | .ok (rest, bitmaps, chunks) =>
                  .ok ((label, wordParameters, stackBody) :: rest, bitmaps, chunks)

def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsChecked
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Except PipelineRiscVLoweringError
        (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState)
  | functions =>
      match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsCheckedAux
          bitmaps [bitmaps.data] functions with
      | .error error => .error error
      | .ok (compiled, finalBitmaps, chunks) =>
          .ok (compiled,
            { data := chunks.reverse.flatten, length := finalBitmaps.length })

/-! Source-shaped sibling of the checked bitmap pipeline.  Pancake's
    `loop_to_word$compile_prog` has already assigned the dense Word names and
    has retained the extra entry slot in the function arity.  Re-running
    `loopToWordCompFunc` from the loop-facing pipeline loses that distinction,
    so the source runtime path must allocate this Word program directly. -/
def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState)
    (chunks : List (List Nat)) :
    List (Nat × Nat × WordProg (RiscV.Word width)) →
      Except PipelineRiscVLoweringError
        (List (Nat × List Nat × StackProg Nat) ×
          RiscV.WordStackBitmapState × List (List Nat))
  | [] => .ok ([], bitmaps, chunks)
  | (label, arity, body) :: functions =>
      let wordParameters := wordSsaAbiParameters arity
      let unallocatedBody :=
        RiscV.wordInstSelectProgramFrom
          (RiscV.wordToWordPreSsa
            (RiscV.wordFlattenProgramFrom body))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, _renamedParameters, renamedProgram, allocation) =>
          let frameSlots :=
            RiscV.cakeWordFrameSlots allocation wordParameters renamedProgram
          -- x23 stays clear of every Cake colour (x29 is colour 12 and can
          -- hold a call argument), so the parallel-move source check never trips.
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := 23
              specialScratch := RiscV.cakeSpecialScratch
              carryScratch := RiscV.cakeCarryScratch
              abiBase := 1
              abiStride := 1
              callAbiBase := 0
              /- The source-shaped call list includes Cake's link slot.  Its
                 register window is the full Cake `k`, not the historical
                 twelve-register value used by the generic RISC-V path. -/
              abiRegisterCount := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              abiFrameSlots := frameSlots
              frameOffset := if frameSlots = 0 then 0 else frameSlots + 1
              sectionId := label
              handlerLabel := label }
          let localState : RiscV.WordStackBitmapState :=
            { data := [], length := bitmaps.length }
          let lower :=
            if frameSlots = 0 then
              RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources
                config wordParameters wordRiscVAbiSourceRegister
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots (some 1) localState renamedProgram
            else
              RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources
                config wordParameters wordRiscVAbiSourceRegister
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots (some 1) localState renamedProgram
          match lower with
          | none =>
              let path := (RiscV.wordProgFirstExpressionLoweringFailure config
                (RiscV.wordProgToNat renamedProgram)).getD []
              .error (.wordToStackFailure label path)
          | some (stackBody, nextBitmaps) =>
              let stackBody := RiscV.stackNormalizeCakeFfi stackBody
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
                  nextBitmaps (nextBitmaps.data :: chunks) functions with
              | .error error => .error error
              | .ok (rest, bitmaps, chunks) =>
                  .ok ((label, wordParameters, stackBody) :: rest, bitmaps, chunks)

def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState)
    (functions : List (Nat × Nat × WordProg (RiscV.Word width))) :
    Except PipelineRiscVLoweringError
      (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState) :=
  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
      bitmaps [bitmaps.data] functions with
  | .error error => .error error
  | .ok (compiled, finalBitmaps, chunks) =>
      .ok (compiled,
        { data := chunks.reverse.flatten, length := finalBitmaps.length })

inductive SourceRiscVCompileError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  | entryNotFound
  | lowering (error : PipelineRiscVLoweringError)
  | loweringInFunction (functionName : FunName) (error : PipelineRiscVLoweringError)
  deriving Repr

structure SourceRiscVArtifact (width : Nat) where
  bytes : List (BitVec 8)
  warnings : List StatErr

inductive SourceRiscVImageError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  | entryNotFound
  | lowering (error : PipelineRiscVLoweringError)
  | loweringInFunction (functionName : FunName) (error : PipelineRiscVLoweringError)
  | artifactFailure
  deriving Repr

def pipelineLoweringSectionId : PipelineRiscVLoweringError → Option Nat
  | .wordToStack error => some error.sectionId
  | .allocationFailure sectionId => some sectionId
  | .wordToStackFailure sectionId _ => some sectionId
  | .labToRiscV error => some error.sectionId
  | .stackToRiscV => none

def compiledFunctionNameAt : List (CompiledFunction α) → Nat → Option FunName
  | [], _ => none
  | function :: _, 0 => some function.name
  | _ :: functions, index + 1 => compiledFunctionNameAt functions index

def pipelineFunctionNameAtLabel (firstLabel : Nat)
    (functions : List (CompiledFunction α)) (label : Nat) : Option FunName :=
  if label < firstLabel then none
  else compiledFunctionNameAt functions (label - firstLabel)

def sourceRiscVCompileErrorOfLowering (firstLabel : Nat)
    (functions : List (CompiledFunction α))
    (error : PipelineRiscVLoweringError) : SourceRiscVCompileError :=
  match pipelineLoweringSectionId error with
  | some label =>
      match pipelineFunctionNameAtLabel firstLabel functions label with
      | some functionName => .loweringInFunction functionName error
      | none => .lowering error
  | none => .lowering error

def sourceRiscVImageErrorOfLowering (firstLabel : Nat)
    (functions : List (CompiledFunction α))
    (error : PipelineRiscVLoweringError) : SourceRiscVImageError :=
  match pipelineLoweringSectionId error with
  | some label =>
      match pipelineFunctionNameAtLabel firstLabel functions label with
      | some functionName => .loweringInFunction functionName error
      | none => .lowering error
  | none => .lowering error

/-- Human-readable name of the pipeline pass that reported a lowering error. -/
def pipelineRiscVLoweringPassName : PipelineRiscVLoweringError → String
  | .wordToStack _ => "word-to-stack"
  | .allocationFailure _ => "register allocation"
  | .wordToStackFailure _ _ => "word-to-stack"
  | .labToRiscV _ => "lab-to-riscv"
  | .stackToRiscV => "stack-to-riscv"

/-- User-facing description of a lowering error.

The `sectionId` inside a lowering error is the position of the failing
function in the crepe list the pass consumed, so it is a pipeline-local label
rather than a stable identity: `--hex` numbers crepe sections from 1 while the
default runtime-image mode numbers them from `stackFunctionFirstLabel`, and the
same failing function is therefore section `n` in one mode and `n + 2` in the
other.  Diagnostics name the containing function when `loweringInFunction`
resolved one and always mark the raw section id as mode-local, while leaving
the Cake-compatible internal labels unchanged. -/
def pipelineRiscVLoweringErrorDescription
    (error : PipelineRiscVLoweringError) : String :=
  match pipelineLoweringSectionId error with
  | some sectionId =>
      s!"{pipelineRiscVLoweringPassName error} failed in mode-local section {sectionId}"
  | none => s!"{pipelineRiscVLoweringPassName error} failed (section id unavailable)"

def sourceRiscVCompileErrorDescription : SourceRiscVCompileError → String
  | .parse errors => s!"parse error: {repr errors}"
  | .static error => s!"static check failed: {repr error}"
  | .entryNotFound => "no entry point named 'main'"
  | .lowering error => pipelineRiscVLoweringErrorDescription error
  | .loweringInFunction functionName error =>
      s!"in function '{functionName}': {pipelineRiscVLoweringErrorDescription error}"

def sourceRiscVImageErrorDescription : SourceRiscVImageError → String
  | .parse errors => s!"parse error: {repr errors}"
  | .static error => s!"static check failed: {repr error}"
  | .entryNotFound => "no entry point named 'main'"
  | .lowering error => pipelineRiscVLoweringErrorDescription error
  | .loweringInFunction functionName error =>
      s!"in function '{functionName}': {pipelineRiscVLoweringErrorDescription error}"
  | .artifactFailure => "failed to assemble a runtime artifact section"

structure SourceRiscVImage (width : Nat) where
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr

structure SourceRiscVRuntimeImage (width : Nat) where
  crepe : List (CompiledFunction (RiscV.Word width))
  bitmaps : RiscV.WordStackBitmapState
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr
  /-- User FFI names in Cake's Lab collector order.  The exporter reverses
      this list when rendering the startup-frame stubs, matching
      `export_riscv`'s `REVERSE ffi_names`. -/
  ffiNames : List String

/-! FFI discovery must observe the same Word simplification boundary as the
    emitted code.  In particular, Cake's `const_fp` removes a branch whose
    comparison is already constant before `export_riscv` collects FFI names.
    The source-shaped `pipeline.word` is intentionally earlier than that
    pass, so applying the faithful pre-allocation Word sequence here avoids
    registering stubs for dead constant branches. -/
def wordFfiDiscoveryBody [NeZero width]
    (body : WordProg (RiscV.Word width)) : WordProg (RiscV.Word width) :=
  RiscV.wordRemoveUnreachable (wordProgDCE
    (RiscV.wordInstSelectProgramFrom
      (RiscV.wordToWordPreSsa (RiscV.wordFlattenProgramFrom body))))

/-! Source-facing entrypoint. Parsing and static checking are kept ahead of
    the existing entry-aware pipeline so callers can distinguish front-end,
    missing-entry, and target-lowering failures. -/
def compileFlapjackRiscVSourceBytesChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Int → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName) (source : String) :
    Except SourceRiscVCompileError (SourceRiscVArtifact width) :=
  match hparse : Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          let parsedByteRanged := Parser.parseTopDecs_declByteRanged
            fromNat source false declarations hparse
          let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
            declarations parsedByteRanged
          match compileFlapjackEntryCake architecture bytesInWord
              (fun value => fromNat value) start
              (panTargetDeclarationsWithDefaultMain declarations)
              (some (.isTrue targetByteRanged)) with
          | none => .error .entryNotFound
          | some pipeline =>
              let sourceLoop := pipelineLoopFunctionsSource architecture 1 pipeline.crepe
              let sourceWord := pipelineWordFunctionsSource sourceLoop
              /- Cake's backend scans the compiled section list from its
                 reverse function order before `export_riscv` reverses the
                 names into the startup-frame stubs.  `compile_prog` keeps
                 this order even though the emitted symbol table is later
                 presented in source order. -/
              let discoveredNames :=
                (sourceWord.reverse.flatMap
                  (fun entry : Nat × List Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNamesCake (wordFfiDiscoveryBody entry.2.2))).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              let identityResult :
                  Except PipelineRiscVLoweringError (List (BitVec 8)) :=
                match RiscV.pipelineWordFunctionsToStackChecked sourceWord with
                | .error error => .error (.wordToStack error)
                | .ok functions =>
                    match RiscV.compileStackProgramNatListWithRaiseStubToRiscVChecked
                        (width := width)
                        { services := services } removeConfig 0 0
                        (functions.map (fun (label, _, body) => (label, body))) with
                    | .error error => .error (.labToRiscV error)
                    | .ok instructions => .ok (RiscV.encodeInstructions instructions)
              match identityResult with
              | .ok bytes => .ok { bytes := bytes, warnings }
              | .error _identityError =>
                  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked pipeline.loop with
                  | .error error =>
                      .error (sourceRiscVCompileErrorOfLowering 1 pipeline.crepe error)
                  | .ok functions =>
                      let initialLabel := fullSsaInitialLabLabel functions
                      match RiscV.compileStackProgramNatListWithRaiseStubToRiscVCakeChecked
                          (width := width)
                          { services := services } removeConfig 0 initialLabel
                          (functions.map (fun (label, _, body) => (label, body))) with
                      | .error error =>
                          .error (sourceRiscVCompileErrorOfLowering 1 pipeline.crepe
                            (.labToRiscV error))
                      | .ok instructions =>
                          .ok { bytes := RiscV.encodeInstructions instructions, warnings }

/-! Linked source-entry image. The full-SSA entry pipeline retains the same
    section labels and byte addresses used by the machine correctness harness;
    encoding is applied section-by-section so that metadata is not lost. -/
def compileFlapjackRiscVSourceImageChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Int → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName) (source : String) :
    Except SourceRiscVImageError (SourceRiscVImage width) :=
  match hparse : Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          let parsedByteRanged := Parser.parseTopDecs_declByteRanged
            fromNat source false declarations hparse
          let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
            declarations parsedByteRanged
          match compileFlapjackEntryCake architecture bytesInWord (fun value => fromNat value)
              start (panTargetDeclarationsWithDefaultMain declarations)
              (some (.isTrue targetByteRanged)) with
          | none => .error .entryNotFound
          | some pipeline =>
              let sourceLoop := pipelineLoopFunctionsSource architecture 1 pipeline.crepe
              let sourceWord := pipelineWordFunctionsSource sourceLoop
              /- Keep FFI discovery in Cake's reverse section order; the
                 artifact exporter reverses this list once more. -/
              let discoveredNames :=
                (sourceWord.reverse.flatMap
                  (fun entry : Nat × List Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNamesCake (wordFfiDiscoveryBody entry.2.2))).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked pipeline.loop with
              | .error error =>
                  .error (sourceRiscVImageErrorOfLowering 1 pipeline.crepe error)
              | .ok functions =>
                  let initialLabel := fullSsaInitialLabLabel functions
                  match RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscVCakeChecked
                      (width := width) { services := services } removeConfig 0 initialLabel
                      (functions.map (fun (label, _, body) => (label, body))) with
                  | .error error =>
                      .error (sourceRiscVImageErrorOfLowering 1 pipeline.crepe
                        (.labToRiscV error))
                  | .ok sections =>
                      .ok { sections := RiscV.encodeLinkedSections sections, warnings }

/-! Runtime image variant carrying the bitmap table emitted by the
    full-SSA SimpleGC pipeline. This is the metadata consumed by the collector
    before the encoded code sections execute. -/
def compileFlapjackRiscVSourceRuntimeImageChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Int → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName) (source : String) :
    Except SourceRiscVImageError (SourceRiscVRuntimeImage width) :=
  match hparse : Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          let parsedByteRanged := Parser.parseTopDecs_declByteRanged
            fromNat source false declarations hparse
          let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
            declarations parsedByteRanged
          match compileFlapjackEntryCake architecture bytesInWord (fun value => fromNat value)
              start (panTargetDeclarationsWithDefaultMain declarations)
              (some (.isTrue targetByteRanged)) with
          | none => .error .entryNotFound
          | some pipeline =>
              let loop := pipelineLoopFunctionsSource architecture stackFunctionFirstLabel
                pipeline.crepe
              let sourceWords := panToWordCompileProg loop
              let discoveryWords :=
                sourceWords.map
                  (fun (label, arity, body) => (label, arity, wordProgDCE body))
              /- The source-shaped list has the same section order after the
                 source loop conversion, so mirror Cake before exporting. -/
              let discoveredNames :=
                (discoveryWords.reverse.flatMap
                  (fun entry : Nat × Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNamesCake (wordFfiDiscoveryBody entry.2.2))).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
                  (RiscV.wordStackInitialBitmaps false) sourceWords with
              | .error error =>
                  .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                    pipeline.crepe error)
              | .ok (functions, bitmaps) =>
                  let initialLabel := fullSsaInitialLabLabel functions
                  match RiscV.compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscVCakeChecked
                      { services := services } removeConfig
                      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
                        firstFreshLabel := stackFunctionFirstLabel }
                      { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                      0 initialLabel
                      (functions.map (fun (label, _, body) => (label, body))) with
                  | .error error =>
                      .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                        pipeline.crepe (.labToRiscV error))
                  | .ok sections =>
                      .ok { crepe := pipeline.crepe, bitmaps,
                            sections := RiscV.encodeLinkedSections sections,
                            warnings, ffiNames := discoveredNames }

end Flapjack
