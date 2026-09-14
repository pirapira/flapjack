import Flapjack.Correctness
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
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    pipelineStackRemoveConfig pipelineHandlerDeclarations

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
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 244 [] image [] []
    (RiscV.writeRegister (RiscV.writeRegister (RiscV.writeRegister
      (RiscV.writeRegister (RiscV.zeroState 64) 1 244) 10 56) 21 288) 8 0)

def pipelineHandlerMachineValues : Option (List (RiscV.Word 64)) := do
  let sections ← pipelineHandlerLinkedSections
  let entry ← pipelineHandlerSectionEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 244 [] image [7] []
    (RiscV.writeRegister (RiscV.writeRegister (RiscV.writeRegister
      (RiscV.writeRegister (RiscV.zeroState 64) 1 244) 10 56) 21 288) 8 0)

#guard pipelineHandlerMachineResult.isSome
#guard pipelineHandlerMachineResult = some []
#guard
  let result := do
    let sections ← pipelineHandlerLinkedSections
    let entry ← pipelineHandlerSectionEntry 2 sections
    let image := sections.flatMap (fun (_, _, code) => code)
    RiscV.executeFunctionAtAfterEntry 4000 0 entry 244 [] image [7] []
      (RiscV.writeRegister (RiscV.writeRegister (RiscV.writeRegister
        (RiscV.writeRegister (RiscV.zeroState 64) 1 244) 10 56) 21 288) 8 0)
  result = some [BitVec.ofNat 64 7]

theorem pipelineHandler_machine_execution :
    pipelineHandlerMachineResult = some [] := by
  native_decide

theorem pipelineHandler_machine_values_execution :
    pipelineHandlerMachineValues = some [BitVec.ofNat 64 7] := by
  native_decide

def pipelineHandlerSourceMachineAgreement : Bool :=
  let sourceResult :=
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20 (fun _ => none)
      pipelineHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => [])
  sourceResult == pipelineHandlerMachineValues

#guard pipelineHandlerSourceMachineAgreement

theorem pipelineHandler_source_machine_simulation :
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20 (fun _ => none)
      pipelineHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = pipelineHandlerMachineValues := by
  calc
    _ = some [BitVec.ofNat 64 7] := pipelineHandler_source_semantics
    _ = _ := pipelineHandler_machine_values_execution.symm

end Flapjack
