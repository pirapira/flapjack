import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeExpressionListRelation
import Flapjack.CrepeSourceWordRecordCorrectness
import Flapjack.CrepeSourceWordLoadCorrectness

/-!
Expression-contract instances for the scalar source fragment.

This is the expression-side companion to the program-level return constructor:
the structural expression simulation supplies the compilation witness, while
the state relation supplies the values of local slots.
-/

namespace Flapjack

theorem panValueCrepExpressionCorrect_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect expression.toExp := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord context hrel.2.1
    (fun name value hvalue =>
      hlookup context sourceLocals name value hvalue)
    expression sourceValue hsource
  cases hword
  have hsourceValue :
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression.toExp =
        some (.word value) := by
    exact hsource
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      (hbytesInWord context bytesInWord) hrel.2.1
      (fun name value hvalue =>
        hlookup context sourceLocals name value hvalue)
      expression value hsourceValue
  refine ⟨by simp, [compiled], ?_, ?_⟩
  · simpa [panValueShape] using hcompile
  · simp [evalCrepFullExps, hcompiled, panValueFlatWords,
      panValueFlatWordsFuel]

theorem panValueCrepExpressionCorrect_load_one
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect (.load .one address.toExp) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord address.toExp with
  | none =>
      simp [evalPanValueExp, haddress] at hsource
  | some addressValue' =>
      obtain ⟨addressValue, haddressWord⟩ := evalPanValueExp_sourceWord_inv
        structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord context hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        address addressValue' haddress
      have hsourceAddress :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord address.toExp =
            some (.word addressValue) := by
        rw [haddress, haddressWord]
      cases hvalue : sourceValue with
      | word value =>
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWord_load_one_relation context structs sourceLocals
              sourceGlobals sourceMemory state baseAddress topAddress bytesInWord
              address addressValue value (hbytesInWord context bytesInWord)
              hrel (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              hsourceAddress (by simpa [hvalue] using hsource)
          refine ⟨panValuePayloadWithinLimit_word structs value, [compiled], ?_, ?_⟩
          · simpa [panValueShape] using hcompile
          · simp [evalCrepFullExps, hcompiled, panValueFlatWords,
              panValueFlatWordsFuel]
      | rStruct fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue,
            panValueFlatLoad, panValueFlatLoadFuel, panValueFlatReadWord] at hsource
      | nStruct name fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue,
            panValueFlatLoad, panValueFlatLoadFuel, panValueFlatReadWord] at hsource

theorem panValueCrepExpressionCorrect_load32
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect (.load32 address.toExp) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord address.toExp with
  | none =>
      simp [evalPanValueExp, haddress] at hsource
  | some addressValue' =>
      obtain ⟨addressValue, haddressWord⟩ := evalPanValueExp_sourceWord_inv
        structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord context hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        address addressValue' haddress
      have hsourceAddress :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord address.toExp =
            some (.word addressValue) := by
        rw [haddress, haddressWord]
      cases hvalue : sourceValue with
      | word value =>
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWord_load32_relation context structs sourceLocals
              sourceGlobals sourceMemory state baseAddress topAddress bytesInWord
              address addressValue value (hbytesInWord context bytesInWord)
              hrel (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              hsourceAddress (by simpa [hvalue] using hsource)
          refine ⟨panValuePayloadWithinLimit_word structs value, [compiled], ?_, ?_⟩
          · simpa [panValueShape] using hcompile
          · simp [evalCrepFullExps, hcompiled, panValueFlatWords,
              panValueFlatWordsFuel]
      | rStruct fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue] at hsource
          cases hmemory : sourceMemory addressValue with
          | none => simp [hmemory] at hsource
          | some stored =>
              cases stored with
              | word stored => simp [hmemory] at hsource
              | rStruct fields => simp [hmemory] at hsource
              | nStruct name fields => simp [hmemory] at hsource
      | nStruct name fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue] at hsource
          cases hmemory : sourceMemory addressValue with
          | none => simp [hmemory] at hsource
          | some stored =>
              cases stored with
              | word stored => simp [hmemory] at hsource
              | rStruct fields => simp [hmemory] at hsource
              | nStruct name fields => simp [hmemory] at hsource

theorem panValueCrepExpressionCorrect_loadByte
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect (.loadByte address.toExp) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord address.toExp with
  | none =>
      simp [evalPanValueExp, haddress] at hsource
  | some addressValue' =>
      obtain ⟨addressValue, haddressWord⟩ := evalPanValueExp_sourceWord_inv
        structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord context hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        address addressValue' haddress
      have hsourceAddress :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord address.toExp =
            some (.word addressValue) := by
        rw [haddress, haddressWord]
      cases hvalue : sourceValue with
      | word value =>
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWord_loadByte_relation context structs sourceLocals
              sourceGlobals sourceMemory state baseAddress topAddress bytesInWord
              address addressValue value (hbytesInWord context bytesInWord)
              hrel (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              hsourceAddress (by simpa [hvalue] using hsource)
          refine ⟨panValuePayloadWithinLimit_word structs value, [compiled], ?_, ?_⟩
          · simpa [panValueShape] using hcompile
          · simp [evalCrepFullExps, hcompiled, panValueFlatWords,
              panValueFlatWordsFuel]
      | rStruct fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue] at hsource
          cases hmemory : sourceMemory addressValue with
          | none => simp [hmemory] at hsource
          | some stored =>
              cases stored with
              | word stored => simp [hmemory] at hsource
              | rStruct fields => simp [hmemory] at hsource
              | nStruct name fields => simp [hmemory] at hsource
      | nStruct name fields =>
          simp [evalPanValueExp, haddress, haddressWord, hvalue] at hsource
          cases hmemory : sourceMemory addressValue with
          | none => simp [hmemory] at hsource
          | some stored =>
              cases stored with
              | word stored => simp [hmemory] at hsource
              | rStruct fields => simp [hmemory] at hsource
              | nStruct name fields => simp [hmemory] at hsource

theorem panValueCrepExpressionCorrect_two_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect
      (.rStruct [left.toExp, right.toExp]) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp with
  | none =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleft] at hsource
  | some leftValue' =>
      obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
        structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord context hrel.2.1
        (fun name value hvalue =>
          hlookup context sourceLocals name value hvalue)
        left leftValue' hleft
      have hleftSource :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord left.toExp =
            some (.word leftValue) := by
        rw [hleft, hleftWord]
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord right.toExp with
      | none =>
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleft, hright] at hsource
      | some rightValue' =>
          obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            right rightValue' hright
          have hrightSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord right.toExp =
                some (.word rightValue) := by
            rw [hright, hrightWord]
          have hsourceValue :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord
                (.rStruct [left.toExp, right.toExp]) =
                some (.rStruct [.word leftValue, .word rightValue]) := by
            simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
              hleftSource, hrightSource]
          have hvalueEq : sourceValue =
              (.rStruct [.word leftValue, .word rightValue] : PanValue α) := by
            exact Option.some.inj (hsource.symm.trans hsourceValue)
          cases hvalueEq
          obtain ⟨compiled, hcompile, hcompiled⟩ :=
            compileSourceWordRecordExp_relation context structs sourceLocals
              sourceGlobals sourceMemory state.locals state.memory
              baseAddress topAddress bytesInWord
              (hbytesInWord context bytesInWord) hrel.2.1
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              [left, right] [leftValue, rightValue]
              (by simpa [evalPanValueExp, evalPanValueExps, Function.comp_def]
                using hsourceValue)
          refine ⟨by simp, compiled, ?_, ?_⟩
          · simpa [panValueShape] using hcompile
          · have hflat :
                panValueFlatWords
                    (.rStruct [.word leftValue, .word rightValue]) =
                  [leftValue, rightValue] := by
              simp [panValueFlatWords, panValueFlatWordsFuel,
                panValueFlatValueFuel,
                panValueFlatWordsFuel.panValueFlatWordsListFuel,
                panValueFlatValueFuel.panValueFlatValueListFuel]
            simpa [hflat] using hcompiled

theorem panValueCrepExpressionCorrect_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (fields : List (SourceWordExp α))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsize : fields.length ≤ 32) :
    PanValueCrepExpressionCorrect
      (.rStruct (fields.map SourceWordExp.toExp)) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  have hsourceDecomp : ∃ values,
      evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord (fields.map SourceWordExp.toExp) =
        some values ∧ .rStruct values = sourceValue := by
    simpa [evalPanValueExp] using hsource
  obtain ⟨values, hfields, hsourceValue⟩ := hsourceDecomp
  obtain ⟨words, hwords, hwordslength⟩ := evalSourceWordExpList_inv
    structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
    bytesInWord context state.locals hrel.2.1
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    fields values (by simpa [evalPanValueExps] using hfields)
  cases hsourceValue
  cases hwords
  have hsourceFields :
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (fields.map SourceWordExp.toExp) =
        some (words.map (fun value => .word value)) := by
    simpa [evalPanValueExps] using hfields
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileSourceWordExp_rStruct_list_relation context structs sourceLocals
      sourceGlobals sourceMemory state.locals state.memory
      baseAddress topAddress bytesInWord
      (hbytesInWord context bytesInWord) hrel.2.1
      (fun name value hvalue =>
        hlookup context sourceLocals name value hvalue)
      fields words hsourceFields
  have hlistFuel : ∀ values : List α,
      panValueFlatValueFuel.panValueFlatValueListFuel
        (values.map PanValue.word) = values.length := by
    intro values
    induction values with
    | nil => simp [panValueFlatValueFuel.panValueFlatValueListFuel]
    | cons value values ih =>
        simp [panValueFlatValueFuel.panValueFlatValueListFuel,
          panValueFlatValueFuel, ih, Nat.add_comm]
  have hsizeFuel : ∀ (fuel : Nat) (values : List α),
      values.length < fuel →
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel fuel structs
          (values.map PanValue.word) = values.length := by
    intro fuel values
    induction values generalizing fuel with
    | nil => intro; simp [panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel]
    | cons value values ih =>
        cases fuel with
        | zero => simp_all
        | succ fuel =>
            intro hlength
            cases fuel with
            | zero => simp_all
            | succ fuel =>
                simp only [List.length_cons] at hlength
                have htail : values.length < fuel + 1 := by omega
                simp [panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
                  panValuePayloadSizeFuel, ih (fuel + 1) htail, Nat.add_comm]
  have hlimit : panValuePayloadWithinLimit structs
      (.rStruct (words.map (fun value => .word value))) = true := by
    simp only [panValuePayloadWithinLimit, panValueFlatValueFuel]
    rw [hlistFuel words]
    have hsize :
        panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel
            (1 + words.length) structs (words.map PanValue.word) = words.length := by
      simpa [Nat.add_comm] using
        hsizeFuel (words.length + 1) words (by omega)
    simp [panValuePayloadSizeFuel, hsize]
    omega
  refine ⟨hlimit, compiled, ?_, ?_⟩
  · simpa [panValueShape, Function.comp_def] using hcompile
  · simpa [panValueFlatWords_rStruct_word_list] using hcompiled

end Flapjack
