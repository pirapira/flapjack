import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeReturnCorrectness

/-!
Recursive correctness for record expressions whose fields are words.

The source retains the record structure while Crep receives the flattened
word list.  This is the structured expression case needed by the original
Pancake correctness induction.
-/

namespace Flapjack

theorem compileSourceWordRecordExp_relation
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
    (hsource : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (fields.map SourceWordExp.toExp) =
      some (values.map (fun value => .word value))) :
    ∃ compiled,
      compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) ∧
      evalCrepFullExps crepLocals crepMemory baseAddress topAddress compiled =
        some values := by
  induction fields generalizing values with
  | nil =>
      cases values with
      | nil =>
          refine ⟨[], ?_, ?_⟩
          · simp [compileExp, compileExp.compileExpList]
          · simp [evalCrepFullExps]
      | cons value values =>
          simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
            ] at hsource
  | cons field fields ih =>
      cases values with
      | nil =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none =>
              simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none =>
                  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                    hfield, htail] at hsource
              | some tailValues =>
                  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                    hfield, htail] at hsource
      | cons value values =>
          cases hfield : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord field.toExp with
          | none =>
              simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                hfield] at hsource
          | some fieldValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (List.map SourceWordExp.toExp fields) with
              | none =>
                  simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                    hfield, htail] at hsource
              | some tailValues =>
                  have hvalues : fieldValue :: tailValues =
                      PanValue.word value :: List.map (fun value =>
                        PanValue.word value) values := by
                    simpa [evalPanValueExps, evalPanValueExp.evalPanValueExps,
                      hfield, htail] using hsource
                  have hfieldValue : fieldValue = .word value := by
                    injection hvalues
                  have htailValues : tailValues =
                      List.map (fun value => .word value) values := by
                    injection hvalues
                  subst fieldValue
                  subst tailValues
                  have hhead : evalPanValueExp structs sourceLocals sourceGlobals
                      sourceMemory baseAddress topAddress bytesInWord field.toExp =
                      some (.word value) := hfield
                  have htail : evalPanValueExps structs sourceLocals sourceGlobals
                      sourceMemory baseAddress topAddress bytesInWord
                      (List.map SourceWordExp.toExp fields) =
                      some (List.map (fun value => .word value) values) := by
                    simpa [evalPanValueExps] using htail
                  obtain ⟨headCompiled, hheadCompile, hheadEval⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
                      sourceMemory crepLocals crepMemory baseAddress topAddress bytesInWord
                      hbytesInWord hlocals hlookup field value hhead
                  obtain ⟨tailCompiled, htailCompile, htailEval⟩ := ih values htail
                  have htailFlat :
                      (compileExp.compileExpList context
                        (List.map SourceWordExp.toExp fields)).flatMap Prod.fst =
                        tailCompiled := by
                    simpa [compileExp] using congrArg Prod.fst htailCompile
                  have htailShapes :
                      (compileExp.compileExpList context
                        (List.map SourceWordExp.toExp fields)).map Prod.snd =
                        List.map (fun _ => Shape.one) values := by
                    simpa [compileExp] using congrArg Prod.snd htailCompile
                  refine ⟨[headCompiled] ++ tailCompiled, ?_, ?_⟩
                  · simp [compileExp, compileExp.compileExpList, hheadCompile,
                      htailFlat, htailShapes]
                  · simp [evalCrepFullExps, hheadEval, htailEval]

theorem panValueFlatWords_rStruct_word_list (values : List α) :
    panValueFlatWords (.rStruct (values.map (fun value => .word value))) = values := by
  have hlistFuel : ∀ values : List α,
      panValueFlatValueFuel.panValueFlatValueListFuel
        (values.map PanValue.word) = values.length := by
    intro values
    induction values with
    | nil => simp [panValueFlatValueFuel.panValueFlatValueListFuel]
    | cons value values ih =>
        simp [panValueFlatValueFuel.panValueFlatValueListFuel,
          panValueFlatValueFuel, ih, Nat.add_comm]
  have hvalueFuel : ∀ values : List α,
      panValueFlatValueFuel (.rStruct (values.map PanValue.word)) =
        values.length + 1 := by
    intro values
    simp only [panValueFlatValueFuel]
    rw [hlistFuel values]
    simpa using (Nat.add_comm 1 values.length)
  have hwordsFuel : ∀ (fuel : Nat) (values : List α),
      values.length < fuel →
      panValueFlatWordsFuel.panValueFlatWordsListFuel fuel
          (values.map PanValue.word) = values := by
    intro fuel values
    induction values generalizing fuel with
    | nil => intro; simp [panValueFlatWordsFuel.panValueFlatWordsListFuel]
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
                simp [panValueFlatWordsFuel.panValueFlatWordsListFuel,
                  panValueFlatWordsFuel, ih (fuel + 1) htail]
  rw [panValueFlatWords, hvalueFuel values]
  simp only [panValueFlatWordsFuel]
  exact hwordsFuel (values.length + 1) values (by omega)

theorem compile_full_pan_value_return_record_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α) (baseAddress topAddress bytesInWord : α)
    (fields : List (SourceWordExp α)) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord 1 sourceLocals sourceGlobals
      sourceMemory (.return (.rStruct (fields.map SourceWordExp.toExp))) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory
        [.rStruct (values.map (fun value => .word value))]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem baseAddress topAddress 1 state
      (compileProg context (.return (.rStruct (fields.map SourceWordExp.toExp)))) =
      some (.returned state
        (panValueFlatWords (.rStruct (values.map (fun value => .word value))))) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory
        [.rStruct (values.map (fun value => .word value))])
      (.returned state
        (panValueFlatWords (.rStruct (values.map (fun value => .word value))))) := by
  have hsourceFields : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (fields.map SourceWordExp.toExp) =
      some (values.map (fun value => .word value)) := by
    simpa [evalPanValueExp, evalPanValueExps, Function.comp_def] using hsource
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileSourceWordRecordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup fields values hsourceFields
  have hcompileShape : compileExp context
      (.rStruct (fields.map SourceWordExp.toExp)) =
      (compiled, panValueShape structs
        (.rStruct (values.map (fun value => .word value)))) := by
    simpa [panValueShape, Function.comp_def] using hcompile
  have hcompiled' : evalCrepFullExps state.locals state.memory
      baseAddress topAddress compiled =
      some (panValueFlatWords
        (.rStruct (values.map (fun value => .word value)))) := by
    simpa [panValueFlatWords_rStruct_word_list] using hcompiled
  exact compile_full_pan_value_return_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    (.rStruct (fields.map SourceWordExp.toExp))
    (.rStruct (values.map (fun value => .word value))) compiled exceptionRel hsource
    hvalid hcompileShape hcompiled' hlocals

end Flapjack
