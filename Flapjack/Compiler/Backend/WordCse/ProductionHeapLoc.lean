import Flapjack.Compiler.Backend.WordCse.ProductionFactAux
import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Compiler.Backend.WordCse.Proofs.WfDataPreservation

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Complete executed OpCurrHeap transition. Original source guards and emitted
source register are retained; canonicalization affects only the fact key.
Flapjack representation infrastructure, with only input relation/original wfData. -/
theorem wordCseHeap_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (operator : BinOp) (destination source : Nat) :
    let nativeOutput := wordCse native (.opCurrHeap operator destination source : WordLangProgHOL (BitVec width))
    let executedOutput := RiscV.wordCseProg executed (.opCurrHeap operator destination source : WordProg (BitVec width))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have invalidRelated := invalidateData_transport native executed related destination
  simp only [wordCse, RiscV.wordCseProg, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases guard : source % 2 = 0 ∨ source = destination
  · simp only [guard, if_pos]
    exact ⟨invalidRelated, rfl⟩
  · simp only [guard, if_false]
    have canonical := canonicalRegsAvoid_transport _ _ invalidRelated destination source
    rw [← canonical]
    have registered := registerRead_transport _ _ invalidRelated
      (canonicalRegs' destination (invalidateData native destination) source)
    have registeredWf := wfData_register_read (invalidateData native destination)
      (canonicalRegs' destination (invalidateData native destination) source)
      (wfData_invalidate native destination wellFormed)
    have output := addToDataAux_production_transport _ _ registered
      registeredWf.2.2.2.2.2.2.2.1 destination
      (opCurrHeapToNumList operator (canonicalRegs' destination (invalidateData native destination) source))
      (.opCurrHeap operator destination source) (.opCurrHeap operator destination source) rfl
    have table : (wordCseRegisterRead (wordCseInvalidate executed destination)
        (canonicalRegs' destination (invalidateData native destination) source)).instrsMem =
        (wordCseInvalidate executed destination).instrsMem := by
      unfold wordCseRegisterRead
      split <;> rfl
    rw [table] at output
    simpa only [wordCseHeapToNumList] using And.intro output.1 output.2.2

/-- Complete executed location-value transition for arbitrary destination and
location, including even destinations and full hit/miss Move selection.
Flapjack representation infrastructure; no output or execution premise. -/
theorem wordCseLocValue_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (destination location : Nat) :
    let nativeOutput := wordCse native (.locValue destination location : WordLangProgHOL (BitVec width))
    let executedOutput := RiscV.wordCseProg executed (.locValue destination location : WordProg (BitVec width))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have invalidRelated := invalidateData_transport native executed related destination
  have invalidWf := wfData_invalidate native destination wellFormed
  have output := addToDataAux_production_transport _ _ invalidRelated
    invalidWf.2.2.2.2.2.2.2.1 destination [48, location]
    (.locValue destination location) (.locValue destination location) rfl
  simpa only [wordCse, RiscV.wordCseProg] using And.intro output.1 output.2.2

end Flapjack.Compiler.Backend.WordCse
