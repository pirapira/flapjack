import Flapjack.Compiler.Backend.WordCse.ProductionConst

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Complete actual instrsMem producer correspondence, including replacement
Move/current-holder selection, both destination parities and all five knowledge
fields. Input program conversion is the actual representation boundary;
no target evaluation or output correspondence is assumed. Flapjack-only
infrastructure, not a HOL theorem port or whole-pass adoption. -/
theorem addToDataAux_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed)
    (valid : Misc.BalancedMap.invariant listCmp native.instrsMem)
    (destination : Nat) (key : List Nat)
    (original : WordLangProgHOL (BitVec width)) (executedOriginal : WordProg (BitVec width))
    (converted : wordLangProgFromHOL original = some executedOriginal) :
    let nativeOutput := addToDataAux native destination key original
    let executedOutput := wordCseAddToFact executed executed.instrsMem destination key executedOriginal
      (fun data register => wordCseRecordInst data register key)
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      Misc.BalancedMap.invariant listCmp nativeOutput.1.instrsMem ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  unfold addToDataAux
  simp only [wordCseRecordInst, wordCseAddToFact, wordCseListLookup]
  rw [← related.2.2.2.1]
  cases observed : Misc.BalancedMap.lookup listCmp key native.instrsMem with
  | some previous =>
      have current : (sptLookup previous native.toLatest).getD previous =
          wordCseLookupAny previous executed.toLatest previous := by
        simp only [wordCseLookupAny, related.2.1]
      by_cases even : destination % 2 = 0
      · simp only [even, if_pos, beq_self_eq_true]
        exact ⟨related, valid, by simp [wordLangProgFromHOL, current]⟩
      · have oddBool : (destination % 2 == 0) = false := beq_eq_false_iff_ne.mpr even
        simp only [even, if_false, oddBool, Bool.false_eq_true]
        exact ⟨registerPair_transport native executed related destination previous previous destination,
          valid, by simp [wordLangProgFromHOL, current]⟩
  | none =>
      by_cases even : destination % 2 = 0
      · simp only [even, if_pos, beq_self_eq_true]
        exact ⟨related, valid, converted⟩
      · have oddBool : (destination % 2 == 0) = false := beq_eq_false_iff_ne.mpr even
        simp only [even, if_false, oddBool, Bool.false_eq_true]
        obtain ⟨outputValid, inserted⟩ := factInsert_transport native.instrsMem executed.instrsMem
          valid related.2.2.2.1 key destination
        have factRelated : KnowledgeRel width
            { native with instrsMem := Misc.BalancedMap.insert listCmp key destination native.instrsMem }
            { executed with instrsMem := wordCseListInsert key destination executed.instrsMem } := by
          exact ⟨related.1, related.2.1, related.2.2.1, inserted, related.2.2.2.2⟩
        exact ⟨registerPair_transport _ _ factRelated destination destination destination destination,
          outputValid, converted⟩

/-- Complete actual loadsMem producer correspondence, including replacement
Move/current-holder selection, both destination parities and all five knowledge
fields. Input program conversion is the actual representation boundary;
no target evaluation or output correspondence is assumed. Flapjack-only
infrastructure, not a HOL theorem port or whole-pass adoption. -/
theorem addToLoadAux_production_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed)
    (valid : Misc.BalancedMap.invariant listCmp native.loadsMem)
    (destination : Nat) (key : List Nat)
    (original : WordLangProgHOL (BitVec width)) (executedOriginal : WordProg (BitVec width))
    (converted : wordLangProgFromHOL original = some executedOriginal) :
    let nativeOutput := addToLoadAux native destination key original
    let executedOutput := wordCseAddToLoad executed destination key executedOriginal
    KnowledgeRel width nativeOutput.1 executedOutput.2 ∧
      Misc.BalancedMap.invariant listCmp nativeOutput.1.loadsMem ∧
      wordLangProgFromHOL nativeOutput.2 = some executedOutput.1 := by
  unfold addToLoadAux
  simp only [wordCseAddToLoad, wordCseAddToFact, wordCseListLookup]
  rw [← related.2.2.2.2]
  cases observed : Misc.BalancedMap.lookup listCmp key native.loadsMem with
  | some previous =>
      have current : (sptLookup previous native.toLatest).getD previous =
          wordCseLookupAny previous executed.toLatest previous := by
        simp only [wordCseLookupAny, related.2.1]
      by_cases even : destination % 2 = 0
      · simp only [even, if_pos, beq_self_eq_true]
        exact ⟨related, valid, by simp [wordLangProgFromHOL, current]⟩
      · have oddBool : (destination % 2 == 0) = false := beq_eq_false_iff_ne.mpr even
        simp only [even, if_false, oddBool, Bool.false_eq_true]
        exact ⟨registerPair_transport native executed related destination previous previous destination,
          valid, by simp [wordLangProgFromHOL, current]⟩
  | none =>
      by_cases even : destination % 2 = 0
      · simp only [even, if_pos, beq_self_eq_true]
        exact ⟨related, valid, converted⟩
      · have oddBool : (destination % 2 == 0) = false := beq_eq_false_iff_ne.mpr even
        simp only [even, if_false, oddBool, Bool.false_eq_true]
        obtain ⟨outputValid, inserted⟩ := factInsert_transport native.loadsMem executed.loadsMem
          valid related.2.2.2.2 key destination
        have factRelated : KnowledgeRel width
            { native with loadsMem := Misc.BalancedMap.insert listCmp key destination native.loadsMem }
            { executed with loadsMem := wordCseListInsert key destination executed.loadsMem } := by
          exact ⟨related.1, related.2.1, related.2.2.1, related.2.2.2.1, inserted⟩
        exact ⟨registerPair_transport _ _ factRelated destination destination destination destination,
          outputValid, converted⟩

end Flapjack.Compiler.Backend.WordCse
