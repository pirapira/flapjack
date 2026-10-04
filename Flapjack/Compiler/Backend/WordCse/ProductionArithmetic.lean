import Flapjack.Compiler.Backend.WordCse.ProductionFactAux
import Flapjack.Compiler.Backend.WordCse.CanonicalArith
import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Compiler.Backend.WordCse.Proofs.WfDataPreservation

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV Compiler.Encoders.Asm Compiler.Backend.StackToLab

/-- Total positional projection of all eight native arithmetic constructors.
Flapjack carrier infrastructure; the separate five-register AddCarry extension
has no native source constructor and is not manufactured by this projection. -/
def executedArithmetic {width : Nat} [NeZero width] : HolArith width → WordArith (BitVec width)
  | .binop op d l r => .binOp op d l r.toWordRegImm
  | .shift op d l r => .shift op d l r.toWordRegImm
  | .div d l r => .div d l r
  | .longMul d1 d2 l r => .longMul d1 d2 l r
  | .longDiv d1 d2 l r q => .longDiv d1 d2 l r q
  | .addCarry d l r carry => .cakeAddCarry d l r carry
  | .addOverflow d l r flag => .addOverflow d l r flag
  | .subOverflow d l r flag => .subOverflow d l r flag

/-- Existing reverse codec recovers every projected native arithmetic payload. -/
theorem executedArithmetic_recover {width : Nat} [NeZero width] (operation : HolArith width) :
    ExecutedCodec.arithFromExecuted? (executedArithmetic operation) = some operation := by
  cases operation <;> simp [executedArithmetic, ExecutedCodec.arithFromExecuted?]

/-- Full returned arithmetic program uses the existing production codec. -/
theorem arithmeticProgram_codec {width : Nat} [NeZero width] (operation : HolArith width) :
    wordLangProgFromHOL (.inst (HolInst.arith operation).toWordLangInst) =
      some (.inst (.arith (executedArithmetic operation))) := by
  cases operation <;> simp [wordLangProgFromHOL, wordLangInstFromHOL,
    wordLangArithFromHOL, HolInst.toWordLangInst, HolArith.toWordLangArith, executedArithmetic]

/-- Full source-to-executed arithmetic transition. Only the input representation
and original wfData are assumed; both sharing guards, every written register,
all five output knowledge fields and the complete returned program are retained.
This is Flapjack representation infrastructure, not a tagged HOL theorem. -/
theorem wordCseArithmetic_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (operation : HolArith width) :
    let nativeOutput := wordCseInst native (.arith operation)
    let executedOutput := RiscV.wordCseInst executed (.arith (executedArithmetic operation))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have classifiers := wordCseArithInfo_native _ _ (executedArithmetic_recover operation)
  have invalidRelated := invalidateRegs_transport native executed related (arithWrites operation)
  have adjustedCodec : ExecutedCodec.arithFromExecuted?
      (wordCseCanonicalArith (wordCseInvalidateRegs executed (arithWrites operation))
        (executedArithmetic operation)) =
      some (canonicalArith (invalidateRegs native (arithWrites operation)) operation) := by
    rw [canonicalArith_transport _ _ invalidRelated, executedArithmetic_recover]
    rfl
  have adjustedClassifiers := wordCseArithInfo_native _ _ adjustedCodec
  simp only [wordCseInst, RiscV.wordCseInst, classifiers.1, classifiers.2.1,
    adjustedClassifiers.2.2.1, adjustedClassifiers.2.2.2]
  have containsFalse (xs : List Nat) (r : Nat) : xs.contains r = false ↔ r ∉ xs := by
    rw [Bool.eq_false_iff]
    exact not_congr (List.contains_iff_mem (as := xs) (a := r))
  by_cases share : canMemArith (canonicalArith (invalidateRegs native (arithWrites operation)) operation) = true ∧
      firstRegOfArith operation ∉ arithReads (canonicalArith (invalidateRegs native (arithWrites operation)) operation)
  · simp only [Bool.and_eq_true, Bool.not_eq_true', containsFalse, share]
    have registered := registerReads_transport _ _ invalidRelated
      (arithReads (canonicalArith (invalidateRegs native (arithWrites operation)) operation))
    have registeredWf := wfData_register_reads
      (arithReads (canonicalArith (invalidateRegs native (arithWrites operation)) operation))
      (invalidateRegs native (arithWrites operation))
      (wfData_invalidate_regs (arithWrites operation) native wellFormed)
    have key := wordCseInstToNumList_native
      (.arith (wordCseCanonicalArith (wordCseInvalidateRegs executed (arithWrites operation))
        (executedArithmetic operation)))
      (.arith (canonicalArith (invalidateRegs native (arithWrites operation)) operation))
      (by simp [wordCseNativeInst?, ExecutedCodec.instFromExecuted?, adjustedCodec])
    simp only [addToData, wordCseAddToData, key]
    have output := addToDataAux_production_transport _ _ registered
      registeredWf.2.2.2.2.2.2.2.1 (firstRegOfArith operation)
      (instToNumList (.arith (canonicalArith (invalidateRegs native (arithWrites operation)) operation)))
      (.inst (HolInst.arith operation).toWordLangInst)
      (.inst (.arith (executedArithmetic operation)))
      (arithmeticProgram_codec operation)
    exact ⟨output.1, output.2.2⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true', containsFalse, share, if_false]
    exact ⟨invalidRelated, arithmeticProgram_codec operation⟩

/-- Complete arithmetic correspondence at both actual program Inst callers.
Flapjack representation assembly with the primitive theorem's input premises. -/
theorem wordCseArithmeticProg_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (wellFormed : wfData width native)
    (operation : HolArith width) :
    let nativeOutput := wordCse native (.inst (HolInst.arith operation).toWordLangInst)
    let executedOutput := RiscV.wordCseProg executed (.inst (.arith (executedArithmetic operation)))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  simpa only [wordCse, RiscV.wordCseProg, HolInst.of_to] using
    wordCseArithmetic_production_transport native executed related wellFormed operation

end Flapjack.Compiler.Backend.WordCse
