import Flapjack.Test.Pipeline
import Flapjack.Correctness

namespace Flapjack

open RiscV

/-! Full-SSA handler regression.  The generated handler label is distinct from
    the call continuation, so the exception path reaches the handler body and
    returns its value through the full-SSA ABI register `x2`. -/

def fullSsaHandlerLinkedSections :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    pipelineStackRemoveConfig pipelineHandlerDeclarations

def fullSsaHandlerSectionEntry (label : Nat)
    : List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else fullSsaHandlerSectionEntry label sections

def fullSsaHandlerMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← fullSsaHandlerLinkedSections
  let entry ← fullSsaHandlerSectionEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 324 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 324)

def fullSsaHandlerSourceMain : Prog (RiscV.Word 64) :=
  .dec "exception" .one (.const (BitVec.ofNat 64 0))
    (.call (some (none, some ("E", "exception",
      .return (.var .local "exception")))) "raise" [])

theorem fullSsaHandler_source_execution :
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20
      (fun _ => none) fullSsaHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 7] := by
  simp [fullSsaHandlerSourceMain, pipelineHandlerSourceFunctions,
    evalPanProgWithHandlers, evalPanCallWithHandlers, evalPanExps,
    evalPanExp, lookupPanFunction, bindPanParameters, updatePanLocal]

#guard fullSsaHandlerLinkedSections.isSome
#guard fullSsaHandlerMachineResult == some [BitVec.ofNat 64 7]

theorem fullSsaHandler_machine_execution :
    fullSsaHandlerMachineResult = some [BitVec.ofNat 64 7] := by
  native_decide

theorem fullSsaHandler_source_machine_agreement :
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20
      (fun _ => none) fullSsaHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 7] ∧
      fullSsaHandlerMachineResult = some [BitVec.ofNat 64 7] := by
  exact ⟨fullSsaHandler_source_execution, fullSsaHandler_machine_execution⟩

end Flapjack
