import Flapjack.Compiler.Backend.WordCse.ProductionStoreErase
import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Clause extraction for the full original Get equation (source545-556).
Flapjack assembly infrastructure, with no standalone HOL declaration: the
tagged recursive `wordCse` (`Transform.lean`) uses it as its `Get` clause.
All four original branches retain the complete native program and store
carriers. Semantic correctness (`word_cseProof` `comp_correct`) is not part of
this module. -/
def getClause {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (store : WordStoreHOL) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  let data := invalidateData data destination
  match data.getsMem.lookup store with
  | none =>
      if destination % 2 = 0 then (data, .get destination store)
      else
        ({ data with
            getsMem := (store, destination) :: data.getsMem,
            toCanonical := sptInsert destination destination data.toCanonical,
            toLatest := sptInsert destination destination data.toLatest }, .get destination store)
  | some previous =>
      let source := (sptLookup previous data.toLatest).getD previous
      if destination % 2 = 0 then (data, .move 1 [(destination, source)])
      else
        ({ data with
            toCanonical := sptInsert destination previous data.toCanonical,
            toLatest := sptInsert previous destination data.toLatest }, .move 1 [(destination, source)])

/-- Both original register-map updates derive complete output knowledge
observations; the store and instruction facts retain their input observations. -/
private theorem registerPair_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (canonicalKey canonicalValue latestKey latestValue : Nat) :
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

/-- Full actual Get boundary. All output knowledge observations and the
complete actual program codec are derived from input knowledge correspondence.
No target execution or output relation is assumed; this is API transport,
not the still-open whole-pass semantic correctness theorem. -/
theorem getClause_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (destination : Nat) (store : WordStoreHOL) :
    let nativeOutput := getClause (width := width) native destination store
    let executedOutput := wordCseProg executed
      (.get destination (wordStoreFromHOL store : WordStore (BitVec width)))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have invalidRelated := invalidateData_transport native executed related destination
  generalize nativeInvalid : invalidateData native destination = nativeData at invalidRelated ⊢
  generalize executedInvalid : wordCseInvalidate executed destination = executedData at invalidRelated ⊢
  have stores := invalidRelated.2.2.1 store
  cases found : nativeData.getsMem.lookup store with
  | none =>
    have actualFound := stores.symm.trans found
    by_cases even : destination % 2 = 0
    · simpa [getClause, wordCseProg, nativeInvalid, executedInvalid, found, actualFound,
        even, wordLangProgFromHOL] using And.intro invalidRelated (rfl :
          wordLangProgFromHOL (.get destination store : WordLangProgHOL (BitVec width)) =
          some (.get destination (wordStoreFromHOL store)))
    · have inserted := knowledgeStoreInsert_transport nativeData executedData invalidRelated store destination
      have updated := registerPair_transport _ _ inserted destination destination destination destination
      simpa [getClause, wordCseProg, nativeInvalid, executedInvalid, found, actualFound,
        even, wordLangProgFromHOL] using And.intro updated (rfl :
          wordLangProgFromHOL (.get destination store : WordLangProgHOL (BitVec width)) =
          some (.get destination (wordStoreFromHOL store)))
  | some previous =>
    have actualFound := stores.symm.trans found
    have latest := invalidRelated.2.1 previous
    by_cases even : destination % 2 = 0
    · simpa [getClause, wordCseProg, nativeInvalid, executedInvalid, found, actualFound,
        even, wordLangProgFromHOL, wordCseLookupAny, latest] using And.intro invalidRelated (rfl :
          wordLangProgFromHOL (.move 1 [(destination, (sptLookup previous nativeData.toLatest).getD previous)] :
            WordLangProgHOL (BitVec width)) = some (.move 1 [(destination, (sptLookup previous nativeData.toLatest).getD previous)]))
    · have updated := registerPair_transport _ _ invalidRelated destination previous previous destination
      simpa [getClause, wordCseProg, nativeInvalid, executedInvalid, found, actualFound,
        even, wordLangProgFromHOL, wordCseLookupAny, latest] using And.intro updated (rfl :
          wordLangProgFromHOL (.move 1 [(destination, (sptLookup previous nativeData.toLatest).getD previous)] :
            WordLangProgHOL (BitVec width)) = some (.move 1 [(destination, (sptLookup previous nativeData.toLatest).getD previous)]))

end Flapjack.Compiler.Backend.WordCse
