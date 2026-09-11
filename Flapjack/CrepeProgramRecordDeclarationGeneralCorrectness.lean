import Flapjack.CrepeProgramDeclarationControlRestoration
import Flapjack.CrepeDeclarationFuelInversion
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation
import Flapjack.CrepeSourceWordRecordDeclarationCorrectness

/-!
Compositional correctness for a two-word record declaration with an arbitrary
correct body.  The declaration case evaluates its source fields, materializes
the corresponding Crep temporaries, applies the body correctness hypothesis in
the extended context, and transports the resulting control relation back to
the outer context.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_dec_two_word_record_general
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (left right : SourceWordExp α) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hname : ∀ (context : CompileContext α),
      lookupInfo name context.vars = none)
    (hfresh : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots ∧ context.maxVar + 2 ∉ oldSlots)
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramCorrect
      (.dec name (.comb [.one, .one])
        (.rStruct [left.toExp, right.toExp]) body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue' =>
          obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun current value hvalue =>
              hlookup context sourceLocals current value hvalue)
            left leftValue' hleft
          have hleftSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord left.toExp =
                some (.word leftValue) := by
            rw [hleft, hleftWord]
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
                evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
          | some rightValue' =>
              obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun current value hvalue =>
                  hlookup context sourceLocals current value hvalue)
                right rightValue' hright
              have hrightSource :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord right.toExp =
                    some (.word rightValue) := by
                rw [hright, hrightWord]
              let sourceValue :=
                (.rStruct [.word leftValue, .word rightValue] : PanValue α)
              let sourceLocals' := updatePanValueMap sourceLocals name sourceValue
              let nextContext := { context with
                vars := (name, (.comb [.one, .one],
                  [context.maxVar + 1, context.maxVar + 2])) :: context.vars
                maxVar := context.maxVar + 2 }
              have hshape :
                  panShapeMatches (panValueShape structs sourceValue)
                    (.comb [.one, .one]) = true := by
                simp [sourceValue, panValueShape, panShapeMatches,
                  panShapeMatches.panShapeListMatches]
              have hread :
                  readCrepLocals
                      (updateCrepLocal
                        (updateCrepLocal state.locals
                          (context.maxVar + 1) leftValue)
                        (context.maxVar + 2) rightValue)
                      [context.maxVar + 1, context.maxVar + 2] =
                    some [leftValue, rightValue] := by
                simp [readCrepLocals, updateCrepLocal]
              have hold : ∀ oldName oldValue oldShape oldSlots,
                  oldName ≠ name →
                  sourceLocals oldName = some oldValue →
                  lookupInfo oldName context.vars = some (oldShape, oldSlots) →
                  panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
                  readCrepLocals state.locals oldSlots =
                    some (panValueFlatWords oldValue) := by
                intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
                exact hrel.2.1 oldName oldValue oldShape oldSlots hsourceOld hlookupOld
              have hrelBody :
                  panValueCrepStateRel structs nextContext sourceLocals'
                    sourceGlobals sourceMemory
                    { state with locals :=
                        (updateCrepLocal
                          (updateCrepLocal state.locals
                            (context.maxVar + 1) leftValue)
                          (context.maxVar + 2) rightValue) } := by
                simpa [nextContext, sourceLocals', sourceValue] using
                  panValueCrepStateRel_extend_record_two_words
                    structs context sourceLocals sourceGlobals sourceMemory state
                    name leftValue rightValue hrel hshape hread hold
                    (hfresh context)
              cases hsourceBody :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord sourceFuel
                    sourceLocals' sourceGlobals sourceMemory body with
              | none =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftSource, hrightSource, sourceLocals', sourceValue,
                    hshape, hsourceBody] at hsource
              | some bodyResult =>
                  have hsourceExpected :
                      evalPanValueProgWithPrimitiveCallsAndFfi
                        primitive sourceHandler structs sourceFunctions
                        baseAddress topAddress bytesInWord (sourceFuel + 1)
                        sourceLocals sourceGlobals sourceMemory
                        (.dec name (.comb [.one, .one])
                          (.rStruct [left.toExp, right.toExp]) body) =
                      some (restorePanValueControlLocal name (sourceLocals name)
                        bodyResult) := by
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                      evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftSource, hrightSource, sourceLocals', sourceValue,
                      hshape, hsourceBody, restorePanValueControlLocal,
                      updatePanValueMap]
                  have hcompileLeftResult := compileSourceWordExp_relation
                    context structs sourceLocals sourceGlobals sourceMemory
                    state.locals state.memory baseAddress topAddress bytesInWord
                    (hbytesInWord context bytesInWord) hrel.2.1
                    (fun current value hvalue =>
                      hlookup context sourceLocals current value hvalue)
                    left leftValue hleftSource
                  obtain ⟨compiledLeft, hcompileLeft, hcrepLeft⟩ :=
                    hcompileLeftResult
                  obtain ⟨compiledRight, hcompileRight, hcrepRight⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory state.locals state.memory
                      baseAddress topAddress bytesInWord
                      (hbytesInWord context bytesInWord) hrel.2.1
                      (fun current value hvalue =>
                        hlookup context sourceLocals current value hvalue)
                      right rightValue hrightSource
                  have hcrepRightAfter := hstable state baseAddress topAddress
                    (context.maxVar + 1) compiledRight rightValue leftValue
                    hcrepRight
                  have hcompile :
                      compileExp context (.rStruct [left.toExp, right.toExp]) =
                        ([compiledLeft, compiledRight], .comb [.one, .one]) := by
                    simp [compileExp, compileExp.compileExpList, hcompileLeft,
                      hcompileRight]
                  have hcompileProg :
                      compileProg context
                          (.dec name (.comb [.one, .one])
                            (.rStruct [left.toExp, right.toExp]) body) =
                        nestedDecs [context.maxVar + 1, context.maxVar + 2]
                          [compiledLeft, compiledRight] (compileProg nextContext body) := by
                    simp [compileProg, hcompile, nextContext, allocatedNames,
                      Shape.shapeSize, List.range, List.range.loop, compileExp,
                      compileExp.compileExpList, hcompileLeft, hcompileRight,
                      lookupInfo, Nat.add_assoc]
                  rw [hcompileProg] at hcrep
                  obtain ⟨targetBodyFuel, bodyCrepResult, htargetFuel,
                    hnested, hrestoreResult⟩ := crepNestedDecsEval_of_eval
                    functions crepPrimitive ffi sharedMem
                    baseAddress topAddress targetFuel state
                    [context.maxVar + 1, context.maxVar + 2]
                    [compiledLeft, compiledRight] (compileProg nextContext body)
                    crepResult (by simp [CrepDistinctNames]) (by simp) hcrep
                  rcases hnested with
                    ⟨leftTarget, hleftTarget, rightTarget, hrightTarget, hbodyEval⟩
                  have hleftEq : leftTarget = leftValue := by
                    exact Option.some.inj (hleftTarget.symm.trans hcrepLeft)
                  cases hleftEq
                  have hrightEq : rightTarget = rightValue := by
                    exact Option.some.inj (hrightTarget.symm.trans hcrepRightAfter)
                  cases hrightEq
                  have hbodyRel' := hbody nextContext structs sourceFunctions
                    functions sourceLocals' sourceGlobals
                    sourceMemory
                    { state with locals :=
                        (updateCrepLocal
                          (updateCrepLocal state.locals
                            (context.maxVar + 1) leftValue)
                          (context.maxVar + 2) rightValue) }
                    primitive sourceHandler crepPrimitive ffi sharedMem
                    baseAddress topAddress bytesInWord sourceFuel targetBodyFuel
                    exceptionRel bodyResult bodyCrepResult hrelBody hsourceBody
                    (by simpa [CrepNestedDecsEval] using hbodyEval)
                  have houterRel := panValueCrepControlRel_restore_two_word_declaration
                    structs context (sourceLocals name) state name
                    (hname context) (hfresh context) exceptionRel
                    bodyResult bodyCrepResult hbodyRel'
                  have hsourceEq :=
                    Option.some.inj (hsourceExpected.symm.trans hsource)
                  have hcrepEq :
                      restoreCrepResultList state.locals
                        [context.maxVar + 1, context.maxVar + 2] bodyCrepResult =
                        crepResult := by
                    exact hrestoreResult
                  rw [hsourceEq, hcrepEq] at houterRel
                  exact houterRel

end Flapjack
