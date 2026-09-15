import Flapjack.Correctness
import Flapjack.Test.Pipeline

namespace Flapjack

open RiscV

/-!
The flat pipeline check in `Pipeline.lean` establishes that handler code is
emitted.  This file keeps the linked-section construction check.  The former
direct-entry machine assertions were removed because they bypass the runtime
frame/continuation protocol and were not valid source-to-machine simulations.
Public Cake-linked output is checked separately by `RiscVArtifactParity`.
-/

def pipelineHandlerLinkedSections :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) := do
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
  let mainLength ←
    match sections.find? (fun (label, _, _) => label == 2) with
    | some (_, _, code) => some code.length
    | none => none
  let returnAddress := entry + BitVec.ofNat 64 (4 * mainLength)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry returnAddress [] image [] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 returnAddress)

def pipelineHandlerMachineValues : Option (List (RiscV.Word 64)) := do
  let sections ← pipelineHandlerLinkedSections
  let entry ← pipelineHandlerSectionEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  let mainLength ←
    match sections.find? (fun (label, _, _) => label == 2) with
    | some (_, _, code) => some code.length
    | none => none
  let returnAddress := entry + BitVec.ofNat 64 (4 * mainLength)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry returnAddress [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 returnAddress)

#guard pipelineHandlerLinkedSections.isSome

end Flapjack
