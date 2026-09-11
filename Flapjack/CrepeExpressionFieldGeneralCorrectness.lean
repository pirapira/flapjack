import Flapjack.CrepeExpressionContractCorrectness
import Flapjack.CrepeSourceWordRecordCorrectness

/-!
Correctness of field selection from a record of scalar source expressions.
This is the non-closed counterpart of the constant-field contract: every
record field is compiled to one Crep expression, and `compileField` selects
the corresponding expression.
-/

namespace Flapjack

theorem compileField_one_selection
    [OfNat α 0]
    (values : List α) (expressions : List (CrepExp α))
    (index : Nat) (value : α)
    (hlength : values.length = expressions.length)
    (hfield : values[index]? = some value) :
    ∃ expression,
      expressions[index]? = some expression ∧
      compileField index (values.map (fun _ => .one)) expressions =
        ([expression], .one) := by
  induction values generalizing expressions index value with
  | nil =>
      simp at hfield
  | cons head tail ih =>
      cases expressions with
      | nil =>
          simp at hlength
      | cons expression expressions =>
          cases index with
          | zero =>
              simp at hfield
              subst value
              refine ⟨expression, by simp, ?_⟩
              simp [compileField]
          | succ index =>
              have htailLength : tail.length = expressions.length := by
                simp at hlength
                exact hlength
              have htailField : tail[index]? = some value := by
                simpa using hfield
              obtain ⟨selected, hselected, hcompile⟩ :=
                ih expressions index value htailLength htailField
              refine ⟨selected, ?_, ?_⟩
              · simpa using hselected
              · simpa [compileField] using hcompile

theorem evalCrepFullExps_index
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α)
    (expressions : List (CrepExp α)) (values : List α)
    (index : Nat) (expression : CrepExp α) (value : α)
    (hexpressions : expressions[index]? = some expression)
    (hvalues : values[index]? = some value)
    (heval : evalCrepFullExps locals memory baseAddress topAddress expressions =
      some values) :
    evalCrepFullExp locals memory baseAddress topAddress expression =
      some value := by
  induction expressions generalizing values index expression value with
  | nil =>
      simp at hexpressions
  | cons head tail ih =>
      cases values with
      | nil =>
          have : False := by
            simp at hvalues
          contradiction
      | cons first rest =>
          cases index with
          | zero =>
              simp at hexpressions hvalues
              subst expression
              subst value
              cases hhead : evalCrepFullExp locals memory baseAddress topAddress head with
              | none => simp [evalCrepFullExps, hhead] at heval
              | some headValue =>
                  cases htail : evalCrepFullExps locals memory baseAddress topAddress tail with
                  | none => simp [evalCrepFullExps, hhead, htail] at heval
                  | some tailValues =>
                      have hheadValue : headValue = first := by
                        have hvalues : headValue :: tailValues = first :: rest := by
                          simpa [evalCrepFullExps, hhead, htail] using heval
                        injection hvalues
                      exact congrArg some hheadValue
          | succ index =>
              have htailExpressions : tail[index]? = some expression := by
                simp only [List.getElem?_cons_succ] at hexpressions
                exact hexpressions
              have htailValues : rest[index]? = some value := by
                simp only [List.getElem?_cons_succ] at hvalues
                exact hvalues
              have htailEval :
                  evalCrepFullExps locals memory baseAddress topAddress tail =
                    some rest := by
                cases hhead : evalCrepFullExp locals memory baseAddress topAddress head with
                | none => simp [evalCrepFullExps, hhead] at heval
                | some headValue =>
                    cases htail : evalCrepFullExps locals memory baseAddress topAddress tail with
                    | none => simp [evalCrepFullExps, hhead, htail] at heval
                    | some tailValues =>
                        have hvalues : headValue :: tailValues = first :: rest := by
                          simpa [evalCrepFullExps, hhead, htail] using heval
                        have htailValues : tailValues = rest := by
                          injection hvalues
                        exact congrArg some htailValues
              exact ih rest index expression value htailExpressions
                htailValues htailEval

theorem evalSourceWordExps_words
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (context : CompileContext α)
    (crepLocals : Nat → Option α)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals
      crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (fields : List (SourceWordExp α))
    (values : List (PanValue α))
    (hsource : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (fields.map SourceWordExp.toExp) =
      some values) :
    ∃ words : List α, values = words.map (fun value => .word value) := by
  induction fields generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨[], rfl⟩
      | cons value values =>
          simp [evalPanValueExp.evalPanValueExps] at hsource
  | cons field fields ih =>
      cases values with
      | nil =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none => simp [evalPanValueExp.evalPanValueExps, hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none => simp [evalPanValueExp.evalPanValueExps, hfield, htail] at hsource
              | some tailValues =>
                  simp [evalPanValueExp.evalPanValueExps, hfield, htail] at hsource
      | cons value values =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none =>
              simp [evalPanValueExp.evalPanValueExps,
                hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                  sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none =>
                  simp [evalPanValueExp.evalPanValueExps,
                    hfield, htail] at hsource
              | some tailValues =>
                  have hvalues : fieldValue :: tailValues = value :: values := by
                    simpa [evalPanValueExp.evalPanValueExps,
                      hfield, htail] using hsource
                  have hfieldWord := evalPanValueExp_sourceWord_inv
                    structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord context hlocals hlookup
                    field fieldValue hfield
                  obtain ⟨fieldWord, hfieldWord⟩ := hfieldWord
                  have htailSource :
                      evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                        sourceMemory baseAddress topAddress bytesInWord
                        (List.map SourceWordExp.toExp fields) =
                      some tailValues := htail
                  obtain ⟨tailWords, htailWords⟩ := ih tailValues htailSource
                  refine ⟨fieldWord :: tailWords, ?_⟩
                  calc
                    value :: values = fieldValue :: tailValues := hvalues.symm
                    _ = PanValue.word fieldWord :: List.map
                        (fun value => PanValue.word value) tailWords := by
                      rw [hfieldWord, htailWords]

theorem compileSourceWordRecordExp_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (fields : List (SourceWordExp α)) (values : List α)
    (hsource : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (fields.map SourceWordExp.toExp) =
      some (values.map (fun value => .word value))) :
    ∃ compiled,
      compileExp.compileExpList context (fields.map SourceWordExp.toExp) =
        compiled.map (fun expression => ([expression], .one)) ∧
      evalCrepFullExps crepLocals crepMemory baseAddress topAddress compiled =
        some values ∧
      compiled.length = values.length := by
  induction fields generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨[], by simp [compileExp.compileExpList],
        by simp [evalCrepFullExps], rfl⟩
      | cons value values =>
          have hfalse : False := by
            have hsource' := hsource
            have hmap : List.map (SourceWordExp.toExp (α := α))
                ([] : List (SourceWordExp α)) = [] := by rfl
            rw [hmap] at hsource'
            simp [evalPanValueExp.evalPanValueExps] at hsource'
          exact hfalse.elim
  | cons field fields ih =>
      cases values with
      | nil =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none => simp [evalPanValueExp.evalPanValueExps, hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none => simp [evalPanValueExp.evalPanValueExps, hfield, htail] at hsource
              | some tailValues =>
                  simp [evalPanValueExp.evalPanValueExps, hfield, htail] at hsource
      | cons value values =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none =>
              simp [evalPanValueExp.evalPanValueExps, hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                  sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none =>
                  simp [evalPanValueExp.evalPanValueExps,
                    hfield, htail] at hsource
              | some tailValues =>
                  have hvalues : fieldValue :: tailValues =
                      PanValue.word value :: List.map (fun value =>
                        PanValue.word value) values := by
                    simpa [evalPanValueExp.evalPanValueExps,
                      hfield, htail] using hsource
                  have hfieldValue : fieldValue = .word value := by
                    injection hvalues
                  have htailValues : tailValues =
                      List.map (fun value => .word value) values := by
                    injection hvalues
                  subst fieldValue
                  subst tailValues
                  obtain ⟨headCompiled, hheadCompile, hheadEval⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory crepLocals crepMemory
                      baseAddress topAddress bytesInWord hbytesInWord hlocals
                      hlookup field value hfield
                  obtain ⟨tailCompiled, htailCompile, htailEval, htailLength⟩ :=
                    ih values htail
                  refine ⟨headCompiled :: tailCompiled, ?_, ?_, ?_⟩
                  · simp [compileExp.compileExpList, hheadCompile,
                      htailCompile]
                  · simp [evalCrepFullExps, hheadEval, htailEval]
                  · simp [htailLength]

theorem list_get_map_word
    (values : List α) (index : Nat) (value : PanValue α)
    (hvalue : (values.map (fun value => .word value))[index]? = some value) :
    ∃ word, value = .word word := by
  induction values generalizing index value with
  | nil => simp at hvalue
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hvalue
          exact ⟨head, hvalue.symm⟩
      | succ index =>
          obtain ⟨word, hword⟩ := ih index value (by simpa using hvalue)
          exact ⟨word, hword⟩

theorem list_flatMap_singletons
    (expressions : List (CrepExp α)) :
    List.flatMap Prod.fst
      (expressions.map (fun expression => ([expression], Shape.one))) =
      expressions := by
  induction expressions with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.map_cons, List.flatMap_cons,
        List.singleton_append, List.append_cons, List.append_nil] using
        congrArg (fun expressions => head :: expressions) ih

theorem panValueCrepExpressionCorrect_rField_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (fields : List (SourceWordExp α)) (index : Nat)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect
      (.rField index (.rStruct (fields.map SourceWordExp.toExp))) := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  cases hrecord : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) with
  | none =>
      simp [evalPanValueExp, hrecord] at hsource
  | some recordValue =>
      cases recordValue with
      | word value =>
          simp [evalPanValueExp, hrecord] at hsource
      | nStruct name values =>
          simp [evalPanValueExp, hrecord] at hsource
      | rStruct recordValues =>
          have hrecordFields :
              evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord
                (fields.map SourceWordExp.toExp) = some recordValues := by
            simpa [evalPanValueExp] using hrecord
          obtain ⟨values, hrecordValues⟩ := evalSourceWordExps_words
            structs sourceLocals sourceGlobals sourceMemory baseAddress
            topAddress bytesInWord context state.locals hrel.2.1
            (fun name value hvalue => hlookup context sourceLocals name value hvalue)
            fields recordValues hrecordFields
          have hselectedRecord : recordValues[index]? = some sourceValue := by
            simpa [evalPanValueExp, hrecord] using hsource
          obtain ⟨value, hsourceValue⟩ := list_get_map_word values index
            sourceValue (by simpa [hrecordValues] using hselectedRecord)
          have hselectedValue : values[index]? = some value := by
            simpa [hsourceValue, hrecordValues] using hselectedRecord
          obtain ⟨compiled, hcompileList, hcompiled, hcompiledLength⟩ :=
            compileSourceWordRecordExp_words context structs sourceLocals
              sourceGlobals sourceMemory state.locals state.memory
              baseAddress topAddress bytesInWord
              (hbytesInWord context bytesInWord) hrel.2.1
              (fun name value hvalue =>
                hlookup context sourceLocals name value hvalue)
              fields values
              (by simpa [hrecordValues] using hrecordFields)
          obtain ⟨selected, hselectedCompile, hcompileField⟩ :=
            compileField_one_selection values compiled index value
              (by
                exact hcompiledLength.symm)
              hselectedValue
          have hvalid : panValuePayloadWithinLimit structs sourceValue = true := by
            simp [hsourceValue, panValuePayloadWithinLimit_word]
          have hshape : values.map (fun _ => Shape.one) =
              compiled.map (fun _ => Shape.one) := by
            clear hrecordValues hselectedRecord hsourceValue hselectedValue
              hcompiled hcompileList hcompileField hselectedCompile
            induction values generalizing compiled with
            | nil =>
                cases compiled with
                | nil => rfl
                | cons head tail => simp at hcompiledLength
            | cons head tail ih =>
                cases compiled with
                | nil => simp at hcompiledLength
                | cons head' tail' =>
                    simp only [List.length_cons] at hcompiledLength
                    have htailLength : tail.length = tail'.length := by omega
                    simp [ih tail' htailLength.symm]
          have hcompileField' := hcompileField
          rw [hshape] at hcompileField'
          have hflat := list_flatMap_singletons compiled
          have hshapes : List.map (Prod.snd ∘
              (fun expression => ([expression], Shape.one))) compiled =
              compiled.map (fun _ => Shape.one) := by
            rfl
          refine ⟨hvalid,
            [selected], ?_, ?_⟩
          · simp [compileExp, hcompileList, hcompileField', hsourceValue,
              panValueShape, Function.comp_def, hflat]
          · have hselectedEval := evalCrepFullExps_index
              state.locals state.memory baseAddress topAddress compiled values
              index selected value hselectedCompile hselectedValue hcompiled
            rw [hsourceValue]
            simp [evalCrepFullExps, hselectedEval, panValueFlatWords,
              panValueFlatWordsFuel]

end Flapjack
