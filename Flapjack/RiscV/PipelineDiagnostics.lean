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
  | labToRiscV (error : RiscV.LabLoweringError)
  | stackToRiscV
  deriving DecidableEq, Repr

inductive SourceRiscVCompileError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  | entryNotFound
  | lowering (error : PipelineRiscVLoweringError)
  deriving Repr

structure SourceRiscVArtifact (width : Nat) where
  bytes : List (BitVec 8)
  warnings : List StatErr

inductive SourceRiscVImageError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  | entryNotFound
  | artifactFailure
  deriving Repr

structure SourceRiscVImage (width : Nat) where
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr

structure SourceRiscVRuntimeImage (width : Nat) where
  bitmaps : RiscV.WordStackBitmapState
  sections : List (RiscV.EncodedRiscVSection width)
  warnings : List StatErr

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
              | .error identityError =>
                  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop with
                  | none => .error (.lowering identityError)
                  | some functions =>
                      let initialLabel := fullSsaInitialLabLabel functions
                      match RiscV.compileStackProgramNatListWithRaiseStubToRiscVChecked
                          (width := width)
                          { services := services } removeConfig 0 initialLabel
                          (functions.map (fun (label, _, body) => (label, body))) with
                      | .error error => .error (.lowering (.labToRiscV error))
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
          match pipelineFindFunction start (structCompileTop (panSimpDecls declarations)) with
          | none => .error .entryNotFound
          | some _ =>
              match compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked
                  architecture bytesInWord (fun value => fromNat value) services
                  removeConfig start declarations with
              | none => .error .artifactFailure
              | some sections =>
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
          match pipelineFindFunction start (structCompileTop (panSimpDecls declarations)) with
          | none => .error .entryNotFound
          | some _ =>
              match compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGcEntryLinked
                  architecture bytesInWord (fun value => fromNat value) services
                  removeConfig start declarations with
              | none => .error .artifactFailure
              | some (bitmaps, sections) =>
                  .ok { bitmaps, sections := RiscV.encodeLinkedSections sections, warnings }

end Flapjack
