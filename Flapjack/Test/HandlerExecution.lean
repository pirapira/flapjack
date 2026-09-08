import Flapjack.Test.Pipeline

namespace Flapjack

open RiscV

/-!
The flat pipeline check in `Pipeline.lean` establishes that handler code is
emitted.  This regression goes one step further: retain the LabLang section
addresses, enter the generated `main` section, and run the linked image on the
executable RISC-V model.  Keeping this in a small file makes the relatively
expensive end-to-end reduction easy to identify in build logs.
-/

def pipelineHandlerLinkedSections :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) := do
  let pipeline := compileFlapjack .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) pipelineHandlerDeclarations
  let functions ← pipelineWordFunctionsToStack pipeline.word
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := [] }
    pipelineStackRemoveConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

def pipelineHandlerSectionEntry (label : Nat)
    : List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else pipelineHandlerSectionEntry label sections

def pipelineHandlerMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← pipelineHandlerLinkedSections
  let entry ← pipelineHandlerSectionEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 100 [] image [] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 100)

#guard pipelineHandlerMachineResult.isSome
#guard pipelineHandlerMachineResult = some []
#guard
  let result := do
    let sections ← pipelineHandlerLinkedSections
    let entry ← pipelineHandlerSectionEntry 2 sections
    let image := sections.flatMap (fun (_, _, code) => code)
    RiscV.executeFunctionAtAfterEntry 4000 0 entry 100 [] image [4] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 100)
  result = some [BitVec.ofNat 64 7]

end Flapjack
