import Flapjack.Compiler.Backend.WordCse.ProductionFactAux
import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Compiler.Backend.WordCse.Proofs.WfDataPreservation

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV Compiler.Encoders.Asm

/-- Actual existing memory carrier projection: zero offset uses mem and a
nonzero offset uses memOffset. Flapjack codec infrastructure with no HOL original. -/
def executedMemoryInst {width : Nat} (operator : WordMemOp)
    (destination address : Nat) (offset : BitVec width) : WordInst (BitVec width) :=
  if offset = 0 then .mem operator destination address
  else .memOffset operator destination address offset

/-- Full original memory instruction payload survives the actual codec,
including every opcode, arbitrary registers and the complete word offset. -/
theorem memoryProgram_codec {width : Nat} [NeZero width]
    (operator : WordMemOp) (destination address : Nat) (offset : BitVec width) :
    wordLangProgFromHOL (.inst (HolInst.mem operator destination (.addr address offset)).toWordLangInst) =
      some (.inst (executedMemoryInst operator destination address offset)) := by
  by_cases zero : offset = 0 <;>
    simp_all [wordLangProgFromHOL, HolInst.toWordLangInst, HolAddr.toWordLangAddr,
      wordLangInstFromHOL, executedMemoryInst]

/-- Complete actual load-table wipe preserves all four unrelated fields.
This is a representation update theorem, not an original HOL declaration. -/
theorem wipeLoads_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) :
    KnowledgeRel width { native with loadsMem := Misc.BalancedMap.empty }
      { executed with loadsMem := ∅ } := by
  exact ⟨related.1, related.2.1, related.2.2.1, related.2.2.2.1, fun _ => rfl⟩

/-- The two actual memory constructors have one complete transition equation.
This equation is about the executed implementation, not a supplied simulation. -/
theorem executedMemoryInst_cse_eq {width : Nat} [NeZero width]
    (executed : WordCseKnowledge) (operator : WordMemOp)
    (destination address : Nat) (offset : BitVec width) :
    RiscV.wordCseInst executed (executedMemoryInst operator destination address offset) =
      if isStore operator then
        (.inst (executedMemoryInst operator destination address offset), { executed with loadsMem := ∅ })
      else
        let data := wordCseInvalidate executed destination
        if destination % 2 = 0 ∨ address % 2 = 0 ∨ address = destination then
          (.inst (executedMemoryInst operator destination address offset), data)
        else
          let canonical := wordCseCanonicalRegs' destination data address
          wordCseAddToLoad (wordCseRegisterRead data canonical) destination
            (loadToNumList operator canonical offset)
            (.inst (executedMemoryInst operator destination address offset)) := by
  by_cases zero : offset = 0
  · subst offset
    simp [executedMemoryInst, RiscV.wordCseInst, wordCseIsStore, wordCseLoadToNumList,
      wordCseMemOpToNum, loadToNumList, wordToNum, Bool.or_eq_true, or_assoc]
  · simp_all [executedMemoryInst, RiscV.wordCseInst, wordCseIsStore,
      wordCseLoadOffsetToNumList_native, Bool.or_eq_true, or_assoc]

/-- Full actual CSE memory-instruction correspondence for every memory opcode,
register/address and positive-width offset. Original wfData discharges the
selected-table invariant through invalidation and read registration. All five
knowledge fields and the complete returned program are derived; no output
relation or target execution premise is supplied. Flapjack representation
infrastructure, not a narrowed tagged HOL compiler theorem. -/
theorem wordCseMemory_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (operator : WordMemOp) (destination address : Nat) (offset : BitVec width) :
    let nativeOutput := wordCseInst native (.mem operator destination (.addr address offset))
    let executedOutput := RiscV.wordCseInst executed
      (executedMemoryInst operator destination address offset)
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  rw [executedMemoryInst_cse_eq]
  simp only [wordCseInst]
  cases store : isStore operator
  · simp only [Bool.false_eq_true, if_false]
    have invalidRelated := invalidateData_transport native executed related destination
    by_cases guarded : destination % 2 = 0 ∨ address % 2 = 0 ∨ address = destination
    · simp only [guarded, if_pos]
      exact ⟨invalidRelated, memoryProgram_codec operator destination address offset⟩
    · simp only [guarded, if_false]
      have canonical := canonicalRegsAvoid_transport _ _ invalidRelated destination address
      rw [← canonical]
      have registered := registerRead_transport _ _ invalidRelated
        (canonicalRegs' destination (invalidateData native destination) address)
      have registeredWf := wfData_register_read (invalidateData native destination)
        (canonicalRegs' destination (invalidateData native destination) address)
        (wfData_invalidate native destination wellFormed)
      have output := addToLoadAux_production_transport _ _ registered
        registeredWf.2.2.2.2.2.2.2.2.2.2 destination
        (loadToNumList operator (canonicalRegs' destination (invalidateData native destination) address) offset)
        _ _ (memoryProgram_codec operator destination address offset)
      exact ⟨output.1, output.2.2⟩
  · simp only [if_true]
    exact ⟨wipeLoads_production_transport native executed related,
      memoryProgram_codec operator destination address offset⟩

/-- The complete memory correspondence at both actual program Inst callers.
Flapjack representation assembly; no additional induction, run or output
hypothesis is added to the primitive result. -/
theorem wordCseMemoryProg_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (operator : WordMemOp) (destination address : Nat) (offset : BitVec width) :
    let nativeOutput := wordCse native
      (.inst (HolInst.mem operator destination (.addr address offset)).toWordLangInst)
    let executedOutput := RiscV.wordCseProg executed
      (.inst (executedMemoryInst operator destination address offset))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  simpa only [wordCse, RiscV.wordCseProg, HolInst.of_to] using
    wordCseMemory_production_transport native executed related wellFormed
      operator destination address offset

end Flapjack.Compiler.Backend.WordCse
