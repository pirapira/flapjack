import Flapjack.Pipeline
import Flapjack.Parser
import Flapjack.RiscV.Encoding
import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.WordDiagnostics

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

namespace Flapjack

inductive PipelineRiscVLoweringError where
  | wordToStack (error : RiscV.PipelineWordLoweringError)
  | allocationFailure (sectionId : Nat)
  | labToRiscV (error : RiscV.LabLoweringError)
  | stackToRiscV
  deriving DecidableEq, Repr

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
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := wordProgDCE (loopToWordProg context body)
      match wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
          wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := 31
              stackBase := 0
              addressScratch := 29
              sectionId := label
              handlerLabel := label }
          match RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
              renamedParameters wordAllocatableRegisters.length config.scratch
              allocation.nextSpill (some 1)
              (RiscV.wordStackInitialBitmaps false) renamedProgram with
          | none => .error (.allocationFailure label)
          | some (stackBody, _) =>
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked functions with
              | .error error => .error error
              | .ok rest => .ok ((label, wordParameters, stackBody) :: rest)

/-! Checked bitmap-threaded sibling of the full-SSA spill pipeline.  The
    bitmap state is part of the runtime artifact, so keep it synchronized with
    the same first-failing section diagnostics used by the byte pipeline. -/
def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsChecked
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Except PipelineRiscVLoweringError
        (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState)
  | [] => .ok ([], bitmaps)
  | (label, parameters, body) :: functions =>
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := wordProgDCE (loopToWordProg context body)
      match wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
          wordParameters unallocatedBody with
      | none => .error (.allocationFailure label)
      | some (_, renamedParameters, renamedProgram, allocation) =>
          let config : RiscV.WordStackConfig :=
            { locations := allocation.locations
              scratch := 31
              stackBase := 0
              addressScratch := 29
              sectionId := label
              handlerLabel := label }
          match RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
              renamedParameters wordAllocatableRegisters.length config.scratch
              (max allocation.nextSpill 1) (some 1) bitmaps renamedProgram with
          | none => .error (.allocationFailure label)
          | some (stackBody, bitmaps) =>
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsChecked
                  bitmaps functions with
              | .error error => .error error
              | .ok (rest, bitmaps) =>
                  .ok ((label, wordParameters, stackBody) :: rest, bitmaps)

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
                    RiscV.wordProgFfiNames entry.2.2)).eraseDups
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
                      match RiscV.compileStackProgramNatListWithRaiseStubToRiscVChecked
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
                    RiscV.wordProgFfiNames entry.2.2)).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked pipeline.loop with
              | .error error =>
                  .error (sourceRiscVImageErrorOfLowering 1 pipeline.crepe error)
              | .ok functions =>
                  let initialLabel := fullSsaInitialLabLabel functions
                  match RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscVChecked
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
              let discoveredNames :=
                (pipeline.word.flatMap
                  (fun entry : Nat × List Nat × WordProg (RiscV.Word width) =>
                    RiscV.wordProgFfiNames entry.2.2)).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let services := services ++ discoveredServices
              let loop := pipelineLoopFunctions architecture stackFunctionFirstLabel pipeline.crepe
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsChecked
                  (RiscV.wordStackInitialBitmaps false) loop with
              | .error error =>
                  .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                    pipeline.crepe error)
              | .ok (functions, bitmaps) =>
                  let initialLabel := fullSsaInitialLabLabel functions
                  match RiscV.compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscVChecked
                      { services := services } removeConfig
                      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
                        firstFreshLabel := stackFunctionFirstLabel }
                      { } stackStoreConstsStubLocation wordAllocatableRegisters.length
                      0 initialLabel
                      (functions.map (fun (label, _, body) => (label, body))) with
                  | .error error =>
                      .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                        pipeline.crepe (.labToRiscV error))
                  | .ok sections =>
                      .ok { bitmaps, sections := RiscV.encodeLinkedSections sections,
                            warnings, ffiNames := discoveredNames }

end Flapjack
