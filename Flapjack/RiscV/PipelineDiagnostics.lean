import Flapjack.Pipeline
import Flapjack.LoopToWord
import Flapjack.Parser
import Flapjack.RiscV.Encoding
import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.WordInstSelect
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
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
          (RiscV.wordFuseConditions
            (RiscV.wordInstSelectProgramFrom
              (RiscV.wordFlattenProgramFrom
                (LoopToWord.loopToWordCompFunc label parameters body)))))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          /- Cake reserves enough `f'` slots for both allocator spills and
             arguments outside the physical ABI window, including nested
             calls whose arity exceeds the formal-parameter count. -/
          let frameSlots := max allocation.nextSpill
            (max (wordParameters.length - 12)
              (RiscV.wordProgMaxCallArguments renamedProgram - 12))
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := 29
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
      let unflattenedBody := wordProgDCE
          (RiscV.wordFuseConditions
            (LoopToWord.loopToWordCompFunc label parameters body))
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
          (RiscV.wordFuseConditions
            (RiscV.wordInstSelectProgramFrom
              (RiscV.wordFlattenProgramFrom
                (LoopToWord.loopToWordCompFunc label parameters body)))))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          /- Cake's IRC frame occupancy only affects the state-threaded
             lowering when the function can emit a bitmap entry.  Running the
             complete Cake allocator for functions with no bitmap site was
             both needlessly expensive and semantically inert.  Keep the
             allocator-derived spill and nested-call bounds below for every
             function, and run the exact Cake occupancy calculation only when
             `wordProgHasBitmapSites` can observe it. -/
          let cakeFrameSlots :=
            if RiscV.wordProgHasBitmapSites renamedProgram then
              RiscV.CakeRegAlloc.cakeWordStackVarCount label wordParameters
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount unflattenedBody
            else 0
          let frameSlots := max cakeFrameSlots
            (max (wordParameters.length - 12)
              (RiscV.wordProgMaxCallArguments renamedProgram - 12))
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := 29
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
      let unflattenedBody := wordProgDCE
        (RiscV.wordFuseConditions body)
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
        (RiscV.wordFuseConditions
          (RiscV.wordInstSelectProgramFrom
            (RiscV.wordFlattenProgramFrom body))))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          let renamedProgram := RiscV.wordProgReverseFfiConstSetup renamedProgram
          let cakeFrameSlots :=
            if RiscV.wordProgHasBitmapSites renamedProgram then
              RiscV.CakeRegAlloc.cakeWordStackVarCount label wordParameters
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount unflattenedBody
            else 0
          let frameSlots := max cakeFrameSlots
            (max (wordParameters.length - 12)
              (RiscV.wordProgMaxCallArguments renamedProgram - 12))
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
              stackBase := 0
              addressScratch := RiscV.cakeAddressScratch
              specialScratch := RiscV.cakeSpecialScratch
              carryScratch := RiscV.cakeCarryScratch
              abiBase := 1
              abiStride := 1
              callAbiBase := 0
              abiFrameSlots := frameSlots
              sectionId := label
              handlerLabel := label }
          let localState : RiscV.WordStackBitmapState :=
            { data := [], length := bitmaps.length }
          let lower :=
            if frameSlots = 0 then
              RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources
                config renamedParameters wordRiscVAbiSourceRegister
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                frameSlots (some 1) localState renamedProgram
            else
              RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources
                config renamedParameters wordRiscVAbiSourceRegister
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

structure SourceRiscVImage (width : Nat) where
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr

structure SourceRiscVRuntimeImage (width : Nat) where
  crepe : List (CompiledFunction (RiscV.Word width))
  bitmaps : RiscV.WordStackBitmapState
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr
  /-- User FFI names in first-appearance order, mirroring the stubs the
      original CakeML backend emits in its startup frame. -/
  ffiNames : List String

/-! Checked sibling of `compileFlapjackRiscVViaStack`.  The historical
    `Option` entrypoint remains available for compatibility; this form makes
    a failed Word section distinguishable from a later StackRemove/Lab/RISC-V
    failure. -/
def compileFlapjackRiscVViaStackChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Except PipelineRiscVLoweringError (List (RiscV.Instruction width)) :=
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  match RiscV.pipelineWordFunctionsToStackChecked pipeline.word with
  | .error error => .error (.wordToStack error)
  | .ok functions =>
      match RiscV.compileStackProgramNatListWithRaiseStubToRiscVChecked
          { services := services } removeConfig 0 0
          (functions.map (fun (label, _, body) => (label, body))) with
      | .ok instructions => .ok instructions
      | .error error => .error (.labToRiscV error)

/-! Artifact-facing sibling of the checked instruction pipeline.  CakeML's
    RISC-V target exposes a little-endian byte list, so keep lowering errors
    intact while applying the concrete encoder only to successful code. -/
def compileFlapjackRiscVViaStackBytesChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Except PipelineRiscVLoweringError (List (BitVec 8)) :=
  (compileFlapjackRiscVViaStackChecked architecture bytesInWord fromNat services
    removeConfig declarations).map RiscV.encodeInstructions

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
  match Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          match compileFlapjackEntry architecture bytesInWord
              (fun value => fromNat value) start declarations with
          | none => .error .entryNotFound
          | some pipeline =>
              let discoveredNames :=
                (pipeline.word.flatMap
                  (fun entry : Nat × List Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              let identityResult :
                  Except PipelineRiscVLoweringError (List (BitVec 8)) :=
                match RiscV.pipelineWordFunctionsToStackChecked pipeline.word with
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
  match Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          match compileFlapjackEntry architecture bytesInWord (fun value => fromNat value)
              start (panTargetDeclarationsWithDefaultMain declarations) with
          | none => .error .entryNotFound
          | some pipeline =>
              let discoveredNames :=
                (pipeline.word.flatMap
                  (fun entry : Nat × List Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
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
  match Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          match compileFlapjackEntry architecture bytesInWord (fun value => fromNat value)
              start (panTargetDeclarationsWithDefaultMain declarations) with
          | none => .error .entryNotFound
          | some pipeline =>
              let loop := pipelineLoopFunctions architecture stackFunctionFirstLabel pipeline.crepe
              let sourceWords := panToWordCompileProg loop
              let discoveryWords :=
                sourceWords.map
                  (fun (label, arity, body) => (label, arity, wordProgDCE body))
              let discoveredNames :=
                (discoveryWords.flatMap
                  (fun entry : Nat × Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
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
