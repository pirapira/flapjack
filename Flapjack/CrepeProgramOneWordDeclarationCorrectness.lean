import Flapjack.CrepeProgramOneWordDeclarationControlRestoration
import Flapjack.CrepeDeclarationFuelInversion
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation

/-!
Compositional correctness for a scalar declaration.

The source declaration binds a named word local, while the Crep lowering
binds one fresh slot.  The body is checked in the extended source/Crep
contexts and the resulting control relation is transported back after the
temporary slot is restored.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_dec_one_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : SourceWordExp α) (body : Prog α)
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
      context.maxVar + 1 ∉ oldSlots) :
    PanValueCrepProgramCorrect
      (.dec name .one expression.toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hvalue] at hsource
      | some sourceValue' =>
          obtain ⟨value, hvalueWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun current value hcurrent =>
              hlookup context sourceLocals current value hcurrent)
            expression sourceValue' hvalue
          have hvalueSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord expression.toExp =
                some (.word value) := by
            rw [hvalue, hvalueWord]
          let sourceValue : PanValue α := .word value
          let sourceLocals' := updatePanValueMap sourceLocals name sourceValue
          let nextContext := { context with
            vars := (name, (.one, [context.maxVar + 1])) :: context.vars
            maxVar := context.maxVar + 1 }
          have hshape :
              panShapeMatches (panValueShape structs sourceValue) .one = true := by
            simp [sourceValue, panValueShape, panShapeMatches]
          have hread :
              readCrepLocals
                  (updateCrepLocal state.locals (context.maxVar + 1) value)
                  [context.maxVar + 1] = some [value] := by
            simp [readCrepLocals, updateCrepLocal]
          have hold : ∀ oldName oldValue oldShape oldSlots,
              oldName ≠ name →
              sourceLocals oldName = some oldValue →
              lookupInfo oldName context.vars = some (oldShape, oldSlots) →
              panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
              readCrepLocals
                  (updateCrepLocal state.locals (context.maxVar + 1) value) oldSlots =
                some (panValueFlatWords oldValue) := by
            intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
            have hnotSlot := hfresh context oldName oldShape oldSlots hne hlookupOld
            have hreadSame := readCrepLocals_update_of_not_mem state.locals
              (context.maxVar + 1) value oldSlots hnotSlot
            exact ⟨(hrel.2.1 oldName oldValue oldShape oldSlots
              hsourceOld hlookupOld).1,
              hreadSame.trans (hrel.2.1 oldName oldValue oldShape oldSlots
                hsourceOld hlookupOld).2⟩
          have hrelBody :
              panValueCrepStateRel structs nextContext sourceLocals'
                sourceGlobals sourceMemory
                { state with locals :=
                    updateCrepLocal state.locals (context.maxVar + 1) value } := by
            refine ⟨hrel.1, ?_, hrel.2.2⟩
            have hlocals := panValueCrepLocalsRel_extend structs context sourceLocals
                sourceLocals'
                (updateCrepLocal state.locals (context.maxVar + 1) value)
                name .one [context.maxVar + 1] sourceValue rfl hshape hread hold
            simpa [nextContext, sourceLocals', sourceValue,
              panValueCrepLocalsRel] using hlocals
          cases hsourceBody :
              evalPanValueProgWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord sourceFuel
                sourceLocals' sourceGlobals sourceMemory body with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hvalueSource, sourceLocals', sourceValue, hshape,
                hsourceBody] at hsource
          | some bodyResult =>
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.dec name .one expression.toExp body) =
                    some (restorePanValueControlLocal name (sourceLocals name)
                      bodyResult) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  evalPanValueExp, evalPanValueExp.evalPanValueExps,
                  hvalueSource, sourceLocals', sourceValue, hshape,
                  hsourceBody, restorePanValueControlLocal,
                  updatePanValueMap]
              obtain ⟨compiled, hcompile, hcompiled⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hcurrent =>
                    hlookup context sourceLocals current value hcurrent)
                  expression value hvalueSource
              have hcompileProg :
                  compileProg context
                      (.dec name .one expression.toExp body) =
                    nestedDecs [context.maxVar + 1] [compiled]
                      (compileProg nextContext body) := by
                simp [compileProg, hcompile, nextContext, allocatedNames,
                  Shape.shapeSize, List.range, List.range.loop, compileExp,
                  lookupInfo, Nat.add_assoc]
              rw [hcompileProg] at hcrep
              obtain ⟨targetBodyFuel, bodyCrepResult, htargetFuel,
                hnested, hrestoreResult⟩ := crepNestedDecsEval_of_eval
                functions crepPrimitive ffi sharedMem
                baseAddress topAddress targetFuel state
                [context.maxVar + 1] [compiled] (compileProg nextContext body)
                crepResult (by simp [CrepDistinctNames]) (by simp) hcrep
              rcases hnested with ⟨targetValue, htargetValue, hbodyEval⟩
              have hvalueEq : targetValue = value := by
                exact Option.some.inj (htargetValue.symm.trans hcompiled)
              cases hvalueEq
              have hbodyRel' := hbody nextContext structs sourceFunctions
                functions sourceLocals' sourceGlobals sourceMemory
                { state with locals :=
                    updateCrepLocal state.locals (context.maxVar + 1) value }
                primitive sourceHandler crepPrimitive ffi sharedMem
                baseAddress topAddress bytesInWord sourceFuel targetBodyFuel
                exceptionRel bodyResult bodyCrepResult hrelBody hsourceBody
                (by simpa [CrepNestedDecsEval] using hbodyEval)
              have houterRel := panValueCrepControlRel_restore_one_word_declaration
                structs context (sourceLocals name) state name
                (hname context) (hfresh context) exceptionRel
                bodyResult bodyCrepResult hbodyRel'
              have hsourceEq :=
                Option.some.inj (hsourceExpected.symm.trans hsource)
              cases hsourceEq
              have hcrepEq :
                  restoreCrepResultList state.locals
                    [context.maxVar + 1] bodyCrepResult = crepResult :=
                hrestoreResult
              cases hcrepEq
              exact houterRel

end Flapjack
