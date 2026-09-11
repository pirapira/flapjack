import Flapjack.CrepeProgramPrimitiveRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level correctness for the structured `addCarry` primitive.

The primitive relation is deliberately parameterised by the source and Crep
handlers.  The compiler correctness predicate quantifies over those handlers,
so a caller must supply their correspondence as an invariant.  The remaining
assumptions state the usual typed destination, slot non-aliasing, and fresh
temporary obligations of the Pancake static checker.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_primitive_addCarry
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (left right carry : SourceWordExp α)
    (hdestination : ∀ (structs : StructContext)
      (sourceLocals : VarName → Option (PanValue α))
      (oldValue newValue : PanValue α),
      sourceLocals name = some oldValue →
      panShapeMatches (panValueShape structs newValue)
        (panValueShape structs oldValue) = true →
      ∃ oldLeft oldRight,
        oldValue = .rStruct [.word oldLeft, .word oldRight])
    (hprimitiveShape : ∀ (handler : PanPrimitiveHandler α)
      (left right carry : α) (result : PanValue α),
      handler .addCarry [.word left, .word right, .word carry] = some result →
      ∃ resultWord carryOut,
        result = .rStruct [.word resultWord, .word carryOut])
    (hprimitiveRel : ∀ (primitive : PanPrimitiveHandler α)
      (crepPrimitive : CrepPrimitiveHandler α)
      (left right carry result carryOut : α),
      primitive .addCarry [.word left, .word right, .word carry] =
        some (.rStruct [.word result, .word carryOut]) →
      crepPrimitive .addCarry [left, right, carry] = some [result, carryOut])
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookupWord : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hlookupDest : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (oldLeft oldRight : α),
      sourceLocals name = some (.rStruct [.word oldLeft, .word oldRight]) →
      ∃ leftSlot rightSlot,
        lookupInfo name context.vars =
          some (.comb [.one, .one], [leftSlot, rightSlot]))
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α)
      (temporary : Nat),
      temporary ∈ [context.maxVar + 1, context.maxVar + 2,
        context.maxVar + 3] →
      state.locals temporary = none)
    (hfreshNe : ∀ (context : CompileContext α)
      (leftSlot rightSlot temporary : Nat),
      lookupInfo name context.vars =
        some (.comb [.one, .one], [leftSlot, rightSlot]) →
      temporary ∈ [context.maxVar + 1, context.maxVar + 2,
        context.maxVar + 3] →
      temporary ≠ leftSlot ∧ temporary ≠ rightSlot)
    (hslots : ∀ (context : CompileContext α)
      (leftSlot rightSlot : Nat),
      lookupInfo name context.vars =
        some (.comb [.one, .one], [leftSlot, rightSlot]) →
      leftSlot ≠ rightSlot)
    (hnoalias : ∀ (context : CompileContext α)
      (leftSlot rightSlot : Nat),
      lookupInfo name context.vars =
        some (.comb [.one, .one], [leftSlot, rightSlot]) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        leftSlot ∉ oldSlots ∧ rightSlot ∉ oldSlots) :
    PanValueCrepProgramCorrect
      (.primitive name .addCarry [left.toExp, right.toExp, carry.toExp]) := by
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
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueExps, evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue' =>
          obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun current value hvalue =>
              hlookupWord context sourceLocals current value hvalue)
            left leftValue' hleft
          have hleftSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord left.toExp =
                some (.word leftValue) := by
            rw [hleft, hleftWord]
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExps, evalPanValueExp.evalPanValueExps, hleft,
                hright] at hsource
          | some rightValue' =>
              obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun current value hvalue =>
                  hlookupWord context sourceLocals current value hvalue)
                right rightValue' hright
              have hrightSource :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord right.toExp =
                    some (.word rightValue) := by
                rw [hright, hrightWord]
              cases hcarry : evalPanValueExp structs sourceLocals sourceGlobals
                  sourceMemory baseAddress topAddress bytesInWord carry.toExp with
              | none =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                    evalPanValueExps, evalPanValueExp.evalPanValueExps, hleft,
                    hright, hcarry] at hsource
              | some carryValue' =>
                  obtain ⟨carryValue, hcarryWord⟩ := evalPanValueExp_sourceWord_inv
                    structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord context hrel.2.1
                    (fun current value hvalue =>
                      hlookupWord context sourceLocals current value hvalue)
                    carry carryValue' hcarry
                  have hcarrySource :
                      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                        baseAddress topAddress bytesInWord carry.toExp =
                        some (.word carryValue) := by
                    rw [hcarry, hcarryWord]
                  have hsourceExps :
                      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
                        baseAddress topAddress bytesInWord
                        [left.toExp, right.toExp, carry.toExp] =
                      some [.word leftValue, .word rightValue, .word carryValue] := by
                    change evalPanValueExp.evalPanValueExps structs sourceLocals
                      sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                      [left.toExp, right.toExp, carry.toExp] =
                        some [.word leftValue, .word rightValue, .word carryValue]
                    simp [evalPanValueExp.evalPanValueExps, hleftSource,
                      hrightSource, hcarrySource]
                  cases hprimitiveResult : primitive .addCarry
                      [.word leftValue, .word rightValue, .word carryValue] with
                  | none =>
                      simp only [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
                      rw [hsourceExps] at hsource
                      simp [hprimitiveResult] at hsource
                  | some primitiveResult =>
                      obtain ⟨result, carryOut, hresult⟩ := hprimitiveShape
                        primitive leftValue rightValue carryValue primitiveResult
                        hprimitiveResult
                      have hshapeOld :
                          ∃ oldValue,
                            sourceLocals name = some oldValue ∧
                            panShapeMatches
                              (panValueShape structs
                                (.rStruct [.word result, .word carryOut]))
                              (panValueShape structs oldValue) = true := by
                        cases hlocal : sourceLocals name with
                        | none =>
                            simp only [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
                            rw [hsourceExps] at hsource
                            simp [hprimitiveResult, hresult, hlocal] at hsource
                        | some oldValue =>
                            refine ⟨oldValue, rfl, ?_⟩
                            have hsource' := hsource
                            simp only [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource'
                            rw [hsourceExps] at hsource'
                            simp [hprimitiveResult, hresult, hlocal] at hsource'
                            exact hsource'.1
                      obtain ⟨oldValue, hlocal, hshapeOld'⟩ := hshapeOld
                      obtain ⟨oldLeft, oldRight, holdValue⟩ :=
                        hdestination structs sourceLocals oldValue
                          (.rStruct [.word result, .word carryOut])
                          hlocal hshapeOld'
                      have hold : sourceLocals name = some
                          (.rStruct [.word oldLeft, .word oldRight]) := by
                        simpa [holdValue] using hlocal
                      obtain ⟨leftSlot, rightSlot, hslot⟩ :=
                        hlookupDest context sourceLocals oldLeft oldRight
                          (by simp [hold])
                      have hresultRel := hprimitiveRel primitive crepPrimitive
                        leftValue rightValue carryValue result carryOut
                        (by simpa [hresult] using hprimitiveResult)
                      have hleftFresh := hfresh context state
                        (context.maxVar + 1) (by simp)
                      have hrightFresh := hfresh context state
                        (context.maxVar + 2) (by simp)
                      have hcarryFresh := hfresh context state
                        (context.maxVar + 3) (by simp)
                      have hleftNe := hfreshNe context leftSlot rightSlot
                        (context.maxVar + 1) hslot (by simp)
                      have hrightNe := hfreshNe context leftSlot rightSlot
                        (context.maxVar + 2) hslot (by simp)
                      have hcarryNe := hfreshNe context leftSlot rightSlot
                        (context.maxVar + 3) hslot (by simp)
                      have hslots' := hslots context leftSlot rightSlot hslot
                      have hnoalias' := hnoalias context leftSlot rightSlot hslot
                      obtain ⟨compiledLeft, hcompileLeft, hcompiledLeft⟩ :=
                        compileSourceWordExp_relation context structs sourceLocals
                          sourceGlobals sourceMemory state.locals state.memory
                          baseAddress topAddress bytesInWord
                          (hbytesInWord context bytesInWord) hrel.2.1
                          (fun current value hvalue =>
                            hlookupWord context sourceLocals current value hvalue)
                          left leftValue hleftSource
                      obtain ⟨compiledRight, hcompileRight, hcompiledRight⟩ :=
                        compileSourceWordExp_relation context structs sourceLocals
                          sourceGlobals sourceMemory state.locals state.memory
                          baseAddress topAddress bytesInWord
                          (hbytesInWord context bytesInWord) hrel.2.1
                          (fun current value hvalue =>
                            hlookupWord context sourceLocals current value hvalue)
                          right rightValue hrightSource
                      obtain ⟨compiledCarry, hcompileCarry, hcompiledCarry⟩ :=
                        compileSourceWordExp_relation context structs sourceLocals
                          sourceGlobals sourceMemory state.locals state.memory
                          baseAddress topAddress bytesInWord
                          (hbytesInWord context bytesInWord) hrel.2.1
                          (fun current value hvalue =>
                            hlookupWord context sourceLocals current value hvalue)
                          carry carryValue hcarrySource
                      have hcompiledRightAfter := hstable state baseAddress topAddress
                        (context.maxVar + 1) compiledRight rightValue leftValue hcompiledRight
                      have hcompiledCarryAfterTemp1 := hstable state baseAddress topAddress
                        (context.maxVar + 1) compiledCarry carryValue leftValue hcompiledCarry
                      have hcompiledCarryAfter := hstable
                        ({ state with locals :=
                            (updateCrepLocal state.locals (context.maxVar + 1) leftValue) } :
                          CrepState α)
                        baseAddress topAddress (context.maxVar + 2) compiledCarry carryValue rightValue
                        hcompiledCarryAfterTemp1
                      have hprimitive' : primitive .addCarry
                          [.word leftValue, .word rightValue, .word carryValue] =
                          some (.rStruct [.word result, .word carryOut]) := by
                        simpa [hresult] using hprimitiveResult
                      have hcompileArgs : compileArgs context
                          [left.toExp, right.toExp, carry.toExp] =
                          [compiledLeft, compiledRight, compiledCarry] := by
                        simp [compileArgs, hcompileLeft, hcompileRight,
                          hcompileCarry]
                      have hcompileProg : compileProg context
                          (.primitive name .addCarry
                            [left.toExp, right.toExp, carry.toExp]) =
                          nestedDecs [context.maxVar + 1, context.maxVar + 2,
                            context.maxVar + 3]
                            [compiledLeft, compiledRight, compiledCarry]
                            (.primitive [leftSlot, rightSlot] .addCarry
                              [context.maxVar + 1, context.maxVar + 2,
                                context.maxVar + 3]) := by
                        have hnames : freshNames context
                            [compiledLeft, compiledRight, compiledCarry].length 1 =
                            [context.maxVar + 1, context.maxVar + 2,
                              context.maxVar + 3] := by
                          simp [freshNames, List.range, List.range.loop,
                            Nat.add_assoc]
                        simp only [compileProg, hslot, hcompileArgs]
                        rw [hnames]
                      rw [hcompileProg] at hcrep
                      cases targetFuel with
                      | zero =>
                          simp [nestedDecs, evalCrepFullProg] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              simp [nestedDecs, evalCrepFullProg] at hcrep
                          | succ targetFuel =>
                              cases targetFuel with
                              | zero =>
                                  simp [nestedDecs, evalCrepFullProg] at hcrep
                              | succ targetFuel =>
                                  cases targetFuel with
                                  | zero =>
                                      simp [nestedDecs, evalCrepFullProg] at hcrep
                                  | succ targetFuel =>
                                      have hresult' :=
                                        compile_full_pan_value_primitive_addCarry_relation_fuel
                                          context structs sourceFunctions functions
                                          sourceLocals sourceGlobals sourceMemory state
                                          primitive sourceHandler crepPrimitive ffi sharedMem
                                          baseAddress topAddress bytesInWord sourceFuel targetFuel
                                          name leftSlot rightSlot left right carry
                                          compiledLeft compiledRight compiledCarry
                                          oldLeft oldRight leftValue rightValue carryValue
                                          result carryOut hslot hold hsourceExps
                                          hcompileLeft hcompileRight hcompileCarry
                                          hcompiledLeft hcompiledRightAfter hcompiledCarryAfter
                                          hprimitive' hresultRel hrel
                                          (fun temporary hmem =>
                                            hfresh context state temporary hmem)
                                          (fun temporary hmem =>
                                            hfreshNe context leftSlot rightSlot temporary
                                              hslot hmem)
                                          hslots' hnoalias'
                                      have hcrepForRelation :
                                          evalCrepFullProg functions crepPrimitive ffi sharedMem
                                              baseAddress topAddress (targetFuel + 4) state
                                              (compileProg context
                                                (.primitive name .addCarry
                                                  [left.toExp, right.toExp, carry.toExp])) =
                                            some crepResult := by
                                        simpa [hcompileProg, Nat.add_assoc] using hcrep
                                      have hsourceEq :=
                                        Option.some.inj (hresult'.1.symm.trans hsource)
                                      have hcrepEq :=
                                        Option.some.inj
                                          (hresult'.2.1.symm.trans hcrepForRelation)
                                      cases hsourceEq
                                      cases hcrepEq
                                      exact hresult'.2.2

end Flapjack
