import Flapjack.Compiler.Backend.WordCse.FactProducers
import Flapjack.Compiler.Backend.WordCse.ProductionFactInsert
import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Input register-map observations imply both updated register-map
observations. This is actual API infrastructure with no HOL original. -/
theorem registerPair_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed)
    (canonicalKey canonicalValue latestKey latestValue : Nat) :
    KnowledgeRel width
      { native with
        toCanonical := sptInsert canonicalKey canonicalValue native.toCanonical,
        toLatest := sptInsert latestKey latestValue native.toLatest }
      { executed with
        toCanonical := wordCseInsert canonicalKey canonicalValue executed.toCanonical,
        toLatest := wordCseInsert latestKey latestValue executed.toLatest } := by
  refine ⟨?_, ?_, related.2.2⟩
  · simpa [mapInsert, wordCseMapInsert] using
      mapInsert_transport native.toCanonical executed.toCanonical related.1 [(canonicalKey, canonicalValue)]
  · simpa [mapInsert, wordCseMapInsert] using
      mapInsert_transport native.toLatest executed.toLatest related.2.1 [(latestKey, latestValue)]

/-- The complete native constant producer agrees with the executed transition
for every destination and word. Both original lookup branches retain all five
knowledge observations and the native fact-tree invariant, and rematerialize
the full Const program. This is Flapjack representation infrastructure without
an independent HOL original, not the whole-pass evaluation theorem. Only
input correspondence and the original native fact invariant are assumed. -/
theorem addToDataConst_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed)
    (valid : Misc.BalancedMap.invariant listCmp native.instrsMem)
    (destination : Nat) (word : BitVec width) :
    let nativeOutput := addToDataConst native destination word
    let executedOutput := wordCseAddToDataConst executed destination word
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      Misc.BalancedMap.invariant listCmp nativeOutput.1.instrsMem ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have keyAgreement : wordCseInstToNumList (.const destination word) =
      instToNumList (.const destination word) :=
    wordCseInstToNumList_native _ _ rfl
  unfold addToDataConst wordCseAddToDataConst
  simp only [keyAgreement, wordCseListLookup]
  rw [← related.2.2.2.1]
  cases observed : Misc.BalancedMap.lookup listCmp (instToNumList (.const destination word)) native.instrsMem with
  | some previous =>
      exact ⟨registerPair_transport native executed related destination previous previous destination,
        valid, rfl⟩
  | none =>
      obtain ⟨outputValid, inserted⟩ := factInsert_transport native.instrsMem executed.instrsMem
        valid related.2.2.2.1 (instToNumList (.const destination word)) destination
      have factRelated : KnowledgeRel width
          { native with instrsMem := (Misc.BalancedMap.insert listCmp
              (instToNumList (.const destination word)) destination native.instrsMem) }
          { executed with instrsMem := (wordCseListInsert
              (instToNumList (.const destination word)) destination executed.instrsMem) } :=
        ⟨related.1, related.2.1, related.2.2.1, inserted, related.2.2.2.2⟩
      exact ⟨registerPair_transport _ _ factRelated destination destination destination destination,
        outputValid, rfl⟩

end Flapjack.Compiler.Backend.WordCse
