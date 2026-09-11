import Flapjack.Pipeline
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
  | stackToRiscV
  deriving DecidableEq, Repr

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
      match RiscV.compileStackProgramNatListWithRaiseStubToRiscV
          { services := services } removeConfig 0 0
          (functions.map (fun (label, _, body) => (label, body))) with
      | some instructions => .ok instructions
      | none => .error .stackToRiscV

end Flapjack
