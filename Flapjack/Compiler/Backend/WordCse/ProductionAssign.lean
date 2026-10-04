import Flapjack.Compiler.Backend.WordCse.ProductionKnowledge
import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Literal actual Assign clause for every executed expression and knowledge
state, including expressions presented before instruction selection. -/
theorem executedAssign_eq {α : Type} [WordCseHash α] (data : WordCseKnowledge)
    (destination : Nat) (value : WordExp α) :
    wordCseProg data (.assign destination value) = (.assign destination value, data) := by
  rw [wordCseProg]

/-- Full original Assign transition agrees with the actual executed CSE for
every native expression and destination. Input knowledge relation is the only
premise; no selected-expression restriction, wfData, target run, or output
assumption is needed. Flapjack carrier infrastructure, not a new HOL port. -/
theorem wordCseAssign_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed)
    (destination : Nat) (value : WordLangExpHOL (BitVec width)) :
    let nativeOutput := wordCse native (.assign destination value)
    let executedOutput := RiscV.wordCseProg executed (.assign destination (wordExpFromHOL value))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  simp only [wordCse, RiscV.wordCseProg]
  exact ⟨related, rfl⟩

end Flapjack.Compiler.Backend.WordCse
