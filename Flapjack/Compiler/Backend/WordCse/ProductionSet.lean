import Flapjack.Compiler.Backend.WordCse.ProductionGet

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

@[hol "cakeml/compiler/backend/word_cseScript.sml" "dest_Var_def"
  (words_as_type_indexed_bitvec)]
def destVar {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Option Nat
  | .var register => some register
  | _ => none

/-- Full original Set clause extraction (source557-573). This is untagged
Flapjack assembly infrastructure: HOL has no standalone Set-clause declaration.
The tagged recursive `wordCse` (`Transform.lean`) uses it as its `Set` clause;
semantic correctness (`word_cseProof` `comp_correct`) is not part of this module. -/
def setClause {width : Nat} [NeZero width] (data : Knowledge)
    (store : WordStoreHOL) (expression : WordLangExpHOL (BitVec width)) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  if store = .currHeap then (emptyData, .set store expression)
  else
    let facts := data.getsMem.filter (fun entry => decide (entry.1 ≠ store))
    match destVar expression with
    | none => ({ data with getsMem := facts }, .set store expression)
    | some source =>
        if source % 2 = 0 then ({ data with getsMem := facts }, .set store expression)
        else
          ({ data with
              getsMem := (store, canonicalRegs data source) :: facts,
              toCanonical := sptInsert source
                ((sptLookup source data.toCanonical).getD source) data.toCanonical }, .set store expression)

private theorem isCurrHeap_codec {width : Nat} (store : WordStoreHOL) :
    wordCseIsCurrHeap (wordStoreFromHOL store : WordStore (BitVec width)) =
      decide (store = .currHeap) := by
  cases store <;> rfl

private theorem canonicalInsert_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (key value : Nat) :
    KnowledgeRel width
      { native with toCanonical := sptInsert key value native.toCanonical }
      { executed with toCanonical := wordCseInsert key value executed.toCanonical } := by
  refine ⟨?_, related.2⟩
  simpa [mapInsert, wordCseMapInsert] using
    mapInsert_transport native.toCanonical executed.toCanonical related.1 [(key, value)]

/-- Complete actual Set boundary for all six original expression constructors
and all store names. Program encoding and every output knowledge observation
are derived from input correspondence alone, without target or output premises. -/
theorem setClause_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (store : WordStoreHOL)
    (expression : WordLangExpHOL (BitVec width)) :
    let nativeOutput := setClause native store expression
    let executedOutput := wordCseProg executed
      (.set (wordStoreFromHOL store : WordStore (BitVec width)) (wordExpFromHOL expression))
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  have encoded : wordLangProgFromHOL (.set store expression) =
      some (.set (wordStoreFromHOL store) (wordExpFromHOL expression)) := by
    simp [wordLangProgFromHOL]
  by_cases curr : store = .currHeap
  · subst store
    simpa [setClause, wordCseProg, wordCseIsCurrHeap, wordStoreFromHOL, wordLangProgFromHOL]
      using And.intro (emptyKnowledgeRel width) encoded
  · have erased := knowledgeStoreErase_transport native executed related store
    cases expression
    case var source =>
      by_cases even : source % 2 = 0
      · simpa [setClause, destVar, wordCseProg, isCurrHeap_codec, curr, even,
          wordExpFromHOL, wordLangProgFromHOL] using And.intro erased encoded
      · have inserted := knowledgeStoreInsert_transport _ _ erased store (canonicalRegs native source)
        have updated := canonicalInsert_transport _ _ inserted source (canonicalRegs native source)
        simpa [setClause, destVar, wordCseProg, isCurrHeap_codec, curr, even,
          wordExpFromHOL, wordLangProgFromHOL, canonicalRegs, wordCseCanonicalRegs,
          wordCseLookupAny, related.1 source] using And.intro updated encoded
    all_goals simpa [setClause, destVar, wordCseProg, isCurrHeap_codec, curr,
      wordExpFromHOL, wordLangProgFromHOL] using And.intro erased encoded

end Flapjack.Compiler.Backend.WordCse
