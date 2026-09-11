import Flapjack.CrepeNestedDecsStability
import Flapjack.CrepeDeclarationFuelInversion
import Flapjack.CrepeProgramDeclarationRestoration
import Flapjack.CrepeSourceWordRecordCorrectness
import Flapjack.CrepeStateRelationExtension
import Flapjack.CrepeProgramRelation

/-!
The generic compositional correctness constructor for ordinary Pancake
declarations.  The expression contract supplies the compiled expressions and
their source/Crep values; this theorem handles the declaration evaluator step,
fresh temporary execution, recursive body simulation, and restoration.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_dec_general
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hname : ∀ (context : CompileContext α),
      lookupInfo name context.vars = none)
    (hfresh : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ allocatedNames context shape →
        temporary ∉ oldSlots)
    (hcompiledFresh : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)),
      ∀ temporary, temporary ∈ allocatedNames context shape →
      ∀ expression ∈ compiled, temporary ∉ crepExpVars expression)
    (hcompile : ∀ (context : CompileContext α),
      ∃ compiledValues,
        compileExp context value = (compiledValues, shape) ∧
        (allocatedNames context shape).length = compiledValues.length)
    (hvalue : ∀ (_context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α),
      ∃ sourceValue,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord value = some sourceValue ∧
        panShapeMatches (panValueShape structs sourceValue) shape = true)
    (hcompiledEval : ∀ (context : CompileContext α)
      (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α)
      (compiledValues : List (CrepExp α)) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      compileExp context value = (compiledValues, shape) →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord value = some sourceValue →
      ∃ values,
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiledValues = some values ∧
        compiledValues.length = values.length ∧
        panValueFlatWords sourceValue = values)
    (hdistinct : ∀ (context : CompileContext α),
      CrepDistinctNames (allocatedNames context shape)) :
    PanValueCrepProgramCorrect (.dec name shape value body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨compiledValues, hcompile, hlength⟩ := hcompile context
      obtain ⟨sourceValue, hvalueEval, hshape⟩ := hvalue context structs
        sourceLocals sourceGlobals sourceMemory baseAddress topAddress bytesInWord
      obtain ⟨values, hcompiled, hvaluesLength, hflat⟩ := hcompiledEval context structs
        sourceLocals sourceGlobals sourceMemory state baseAddress topAddress
        bytesInWord compiledValues sourceValue hrel hcompile hvalueEval
      have hnamesValues : (allocatedNames context shape).length = values.length :=
        hlength.trans hvaluesLength
      let sourceLocals' := updatePanValueMap sourceLocals name sourceValue
      let nextContext := { context with
        vars := (name, (shape, allocatedNames context shape)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape }
      cases hsourceBody :
          evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals'
            sourceGlobals sourceMemory body with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalueEval,
            hshape, hsourceBody, sourceLocals'] at hsource
      | some bodyResult =>
          have hsourceExpected :
              evalPanValueProgWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord (sourceFuel + 1)
                sourceLocals sourceGlobals sourceMemory
                (.dec name shape value body) =
              some (restorePanValueControlLocal name
                (sourceLocals name) bodyResult) := by
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalueEval,
              hshape, hsourceBody, sourceLocals',
              restorePanValueControlLocal, updatePanValueMap]
          have hcompileProg :
              compileProg context (.dec name shape value body) =
                nestedDecs (allocatedNames context shape) compiledValues
                  (compileProg nextContext body) := by
            simp [compileProg, hcompile, hlength, nextContext]
          rw [hcompileProg] at hcrep
          obtain ⟨bodyFuel, bodyCrepResult, htargetFuel,
            hnested, hrestoreResult⟩ := crepNestedDecsEval_of_eval
              functions crepPrimitive ffi sharedMem baseAddress topAddress
              targetFuel state (allocatedNames context shape) compiledValues
              (compileProg nextContext body) crepResult
              (hdistinct context) hlength hcrep
          have hnot : ∀ temporary ∈ allocatedNames context shape,
              ∀ expression ∈ compiledValues,
                temporary ∉ crepExpVars expression := by
            exact hcompiledFresh context compiledValues
          have hbodyEval := crepNestedDecsEval_body_of_evalExps_stable
            functions crepPrimitive ffi sharedMem baseAddress topAddress bodyFuel
            state (allocatedNames context shape) compiledValues
            (compileProg nextContext body) bodyCrepResult values hlength hnot
            hcompiled hnested
          have hread := readCrepLocals_updateCrepLocalList state.locals
            (allocatedNames context shape) values hnamesValues (hdistinct context)
          have hold : ∀ oldName oldValue oldShape oldSlots,
              oldName ≠ name →
              sourceLocals oldName = some oldValue →
              lookupInfo oldName context.vars = some (oldShape, oldSlots) →
              panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
              readCrepLocals
                  (updateCrepLocalList state.locals
                    (allocatedNames context shape) values) oldSlots =
                some (panValueFlatWords oldValue) := by
            intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
            have holdValue := hrel.2.1 oldName oldValue oldShape oldSlots
              hsourceOld hlookupOld
            have hnotOld : ∀ temporary ∈ allocatedNames context shape,
                temporary ∉ oldSlots :=
              fun temporary htemporary =>
                hfresh context oldName oldShape oldSlots hne hlookupOld
                  temporary htemporary
            have hreadSame :=
              readCrepLocals_updateCrepLocalList_of_not_mem state.locals
                (allocatedNames context shape) values oldSlots hnamesValues hnotOld
            exact ⟨holdValue.1, hreadSame.trans holdValue.2⟩
          have hrelUpdated :
              panValueCrepStateRel structs context sourceLocals sourceGlobals
                sourceMemory
                { state with
                    locals := updateCrepLocalList state.locals
                      (allocatedNames context shape) values } := by
            refine ⟨hrel.1, ?_, hrel.2.2⟩
            intro current currentValue currentShape currentSlots hcurrent
              hlookupCurrent
            have hne : current ≠ name := by
              intro heq
              subst current
              rw [hname context] at hlookupCurrent
              cases hlookupCurrent
            have holdCurrent := hrel.2.1 current currentValue currentShape
              currentSlots hcurrent hlookupCurrent
            have hnotCurrent : ∀ temporary ∈ allocatedNames context shape,
                temporary ∉ currentSlots := by
              intro temporary htemporary
              exact hfresh context current currentShape currentSlots hne
                hlookupCurrent temporary htemporary
            have hreadCurrent :=
              readCrepLocals_updateCrepLocalList_of_not_mem state.locals
                (allocatedNames context shape) values currentSlots hnamesValues
                hnotCurrent
            exact ⟨holdCurrent.1, hreadCurrent.trans holdCurrent.2⟩
          have hrelBody :
              panValueCrepStateRel structs nextContext sourceLocals'
                sourceGlobals sourceMemory
                { state with
                    locals := updateCrepLocalList state.locals
                      (allocatedNames context shape) values } := by
            simpa [nextContext, panValueCrepStateRel,
              panValueCrepLocalsRel] using
              (panValueCrepStateRel_extend structs context sourceLocals
                sourceLocals' sourceGlobals sourceMemory
                { state with
                    locals := updateCrepLocalList state.locals
                      (allocatedNames context shape) values }
                name shape (allocatedNames context shape) sourceValue
                (by rfl) hshape
                (by simpa [hflat] using hread) hold hrelUpdated)
          have hbodyRelFinal := hbody nextContext structs sourceFunctions
            functions sourceLocals' sourceGlobals sourceMemory
            { state with
                locals := updateCrepLocalList state.locals
                  (allocatedNames context shape) values }
            primitive sourceHandler crepPrimitive ffi sharedMem
            baseAddress topAddress bytesInWord sourceFuel bodyFuel
            exceptionRel bodyResult bodyCrepResult hrelBody hsourceBody
            hbodyEval
          have houterRel := panValueCrepControlRel_restore_declaration
            structs context (sourceLocals name) state name shape
            (allocatedNames context shape) (hname context)
            (fun oldName oldShape oldSlots hne hlookupOld temporary htemp =>
              hfresh context oldName oldShape oldSlots hne hlookupOld
                temporary htemp)
            exceptionRel bodyResult bodyCrepResult hbodyRelFinal
          have hsourceEq :=
            Option.some.inj (hsourceExpected.symm.trans hsource)
          cases hsourceEq
          rw [hrestoreResult] at houterRel
          exact houterRel

end Flapjack
