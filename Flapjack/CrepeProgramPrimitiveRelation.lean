import Flapjack.CrepeProgramAssignmentFuelRelation
import Flapjack.CrepePrimitiveRelation

/-!
Fuel-polymorphic source-to-Crep correctness for the structured `addCarry`
primitive.  The compiler evaluates each scalar argument in a fresh local,
then invokes Crep's flattened primitive handler and restores those locals.
-/

namespace Flapjack

def updateCrepTwoLocals (locals : Nat → Option α)
    (leftSlot rightSlot : Nat) (left right : α) : Nat → Option α :=
  updateCrepLocal (updateCrepLocal locals leftSlot left) rightSlot right

def updateCrepStateTwoLocals (state : CrepState α)
    (leftSlot rightSlot : Nat) (left right : α) : CrepState α :=
  { state with locals := updateCrepTwoLocals state.locals leftSlot rightSlot left right }

theorem panValueCrepLocalsRel_update_two_words
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (leftSlot rightSlot : Nat)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : lookupInfo name context.vars =
      some (Shape.comb [.one, .one], [leftSlot, rightSlot]))
    (hleftValue hrightValue : α)
    (hslots : leftSlot ≠ rightSlot)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      leftSlot ∉ oldSlots ∧ rightSlot ∉ oldSlots) :
    panValueCrepLocalsRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct [.word hleftValue, .word hrightValue]))
      (updateCrepLocal (updateCrepLocal crepLocals leftSlot hleftValue)
        rightSlot hrightValue) := by
  intro current currentValue currentShape currentSlots hcurrent hcurrentLookup
  by_cases hname : current = name
  · subst current
    have hpair : (Shape.comb [.one, .one], [leftSlot, rightSlot]) =
        (currentShape, currentSlots) := by
      have hlookup' : some (Shape.comb [.one, .one], [leftSlot, rightSlot]) =
          some (currentShape, currentSlots) := by
        simpa [hlookup] using hcurrentLookup
      exact Option.some.inj hlookup'
    have hshape : currentShape = Shape.comb [.one, .one] :=
      (congrArg Prod.fst hpair).symm
    have hslots : currentSlots = [leftSlot, rightSlot] :=
      (congrArg Prod.snd hpair).symm
    cases hshape
    cases hslots
    have hvalue : currentValue =
        PanValue.rStruct [.word hleftValue, .word hrightValue] := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    constructor
    · simp [panValueShape, panShapeMatches,
        panShapeMatches.panShapeListMatches]
    · simp [readCrepLocals, updateCrepLocal, panValueFlatWords,
        panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel, hslots] <;> rfl
  · have hcurrentOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hname] using hcurrent
    have hold := hrel current currentValue currentShape currentSlots
      hcurrentOld hcurrentLookup
    have hnot := hnoalias current currentShape currentSlots hname
      hcurrentLookup
    have hleftRead := readCrepLocals_update_of_not_mem crepLocals
      leftSlot hleftValue currentSlots hnot.1
    have hrightRead := readCrepLocals_update_of_not_mem
      (updateCrepLocal crepLocals leftSlot hleftValue)
      rightSlot hrightValue currentSlots hnot.2
    exact ⟨hold.1, by
      rw [hrightRead, hleftRead]
      exact hold.2⟩

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_primitive_addCarry_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (leftSlot rightSlot : Nat)
    (left right carry : SourceWordExp α)
    (compiledLeft compiledRight compiledCarry : CrepExp α)
    (oldLeft oldRight leftValue rightValue carryValue result carryOut : α)
    (hlookup : lookupInfo name context.vars =
      some (.comb [.one, .one], [leftSlot, rightSlot]))
    (hold : sourceLocals name = some
      (.rStruct [.word oldLeft, .word oldRight]))
    (hsourceExps : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord [left.toExp, right.toExp, carry.toExp] =
      some [.word leftValue, .word rightValue, .word carryValue])
    (hcompileLeft : compileExp context left.toExp = ([compiledLeft], .one))
    (hcompileRight : compileExp context right.toExp = ([compiledRight], .one))
    (hcompileCarry : compileExp context carry.toExp = ([compiledCarry], .one))
    (hcompiledLeft : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledLeft = some leftValue)
    (hcompiledRightAfter : evalCrepFullExp
      (updateCrepLocal state.locals (context.maxVar + 1) leftValue)
      state.memory baseAddress topAddress compiledRight = some rightValue)
    (hcompiledCarryAfter : evalCrepFullExp
      (updateCrepLocal
        (updateCrepLocal state.locals (context.maxVar + 1) leftValue)
        (context.maxVar + 2) rightValue)
      state.memory baseAddress topAddress compiledCarry = some carryValue)
    (hprimitive : primitive .addCarry
      [.word leftValue, .word rightValue, .word carryValue] =
      some (.rStruct [.word result, .word carryOut]))
    (hcrepPrimitive : crepPrimitive .addCarry
      [leftValue, rightValue, carryValue] = some [result, carryOut])
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hfresh : ∀ temporary ∈
      [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3],
      state.locals temporary = none)
    (hfreshNe : ∀ temporary ∈
      [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3],
      temporary ≠ leftSlot ∧ temporary ≠ rightSlot)
    (hslots : leftSlot ≠ rightSlot)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      leftSlot ∉ oldSlots ∧ rightSlot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.primitive name .addCarry [left.toExp, right.toExp, carry.toExp]) =
      some (.normal (updatePanValueMap sourceLocals name
        (.rStruct [.word result, .word carryOut])) sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 4) state
      (compileProg context
        (.primitive name .addCarry [left.toExp, right.toExp, carry.toExp])) =
      some (.normal (updateCrepStateTwoLocals state leftSlot rightSlot result carryOut)) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct [.word result, .word carryOut])) sourceGlobals sourceMemory
      (updateCrepStateTwoLocals state leftSlot rightSlot result carryOut) := by
  have hcompileArgs : compileArgs context
      [left.toExp, right.toExp, carry.toExp] =
      [compiledLeft, compiledRight, compiledCarry] := by
    simp [compileArgs, hcompileLeft, hcompileRight, hcompileCarry]
  have hcompileProg : compileProg context
      (.primitive name .addCarry [left.toExp, right.toExp, carry.toExp]) =
      nestedDecs [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3]
        [compiledLeft, compiledRight, compiledCarry]
        (.primitive [leftSlot, rightSlot] .addCarry
          [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3]) := by
    have hnames : freshNames context [compiledLeft, compiledRight, compiledCarry].length 1 =
        [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3] := by
      simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
    simp only [compileProg, hlookup, hcompileArgs]
    rw [hnames]
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceExps,
      hprimitive, hold, panValueShape, panShapeMatches,
      panShapeMatches.panShapeListMatches]
  constructor
  · have hleftFresh := hfresh (context.maxVar + 1) (by simp)
    have hrightFresh := hfresh (context.maxVar + 2) (by simp)
    have hcarryFresh := hfresh (context.maxVar + 3) (by simp)
    have hleftNe := hfreshNe (context.maxVar + 1) (by simp)
    have hrightNe := hfreshNe (context.maxVar + 2) (by simp)
    have hcarryNe := hfreshNe (context.maxVar + 3) (by simp)
    have htemp12 : context.maxVar + 1 ≠ context.maxVar + 2 := by omega
    have htemp13 : context.maxVar + 1 ≠ context.maxVar + 3 := by omega
    have htemp23 : context.maxVar + 2 ≠ context.maxVar + 3 := by omega
    have htemp21 : context.maxVar + 2 ≠ context.maxVar + 1 := Ne.symm htemp12
    have htemp31 : context.maxVar + 3 ≠ context.maxVar + 1 := Ne.symm htemp13
    have htemp32 : context.maxVar + 3 ≠ context.maxVar + 2 := Ne.symm htemp23
    have hleftNe' : leftSlot ≠ context.maxVar + 1 := Ne.symm hleftNe.1
    have hrightNe' : rightSlot ≠ context.maxVar + 1 := Ne.symm hleftNe.2
    have hleftNe'' : leftSlot ≠ context.maxVar + 2 := Ne.symm hrightNe.1
    have hrightNe'' : rightSlot ≠ context.maxVar + 2 := Ne.symm hrightNe.2
    have hleftNe''' : leftSlot ≠ context.maxVar + 3 := Ne.symm hcarryNe.1
    have hrightNe''' : rightSlot ≠ context.maxVar + 3 := Ne.symm hcarryNe.2
    have hslots' : rightSlot ≠ leftSlot := Ne.symm hslots
    have hrestore :
        restoreCrepLocal
            (restoreCrepLocal
              (restoreCrepLocal
                (updateCrepLocal
                  (updateCrepLocal
                    (updateCrepLocal
                      (updateCrepLocal
                        (updateCrepLocal state.locals (context.maxVar + 1) leftValue)
                        (context.maxVar + 2) rightValue)
                      (context.maxVar + 3) carryValue)
                    leftSlot result)
                  rightSlot carryOut)
                (context.maxVar + 3) none)
              (context.maxVar + 2) none)
            (context.maxVar + 1) none =
          updateCrepTwoLocals state.locals leftSlot rightSlot result carryOut := by
      funext current
      by_cases h1 : current = context.maxVar + 1
      <;> by_cases h2 : current = context.maxVar + 2
      <;> by_cases h3 : current = context.maxVar + 3
      <;> by_cases hl : current = leftSlot
      <;> by_cases hr : current = rightSlot
      <;> simp [restoreCrepLocal, updateCrepLocal, updateCrepTwoLocals,
        h1, h2, h3, hl, hr, htemp12, htemp13, htemp23,
        htemp21, htemp31, htemp32, hleftNe', hrightNe', hleftNe'',
        hrightNe'', hleftNe''', hrightNe''', hslots', hleftFresh,
        hrightFresh, hcarryFresh,
        hleftNe.1, hleftNe.2, hrightNe.1, hrightNe.2,
        hcarryNe.1, hcarryNe.2, hslots] <;> omega
    simp [nestedDecs, evalCrepFullProg, updateCrepStateTwoLocals,
      updateCrepTwoLocals, hcompiledLeft, hcompiledRightAfter,
      hcompiledCarryAfter, hleftFresh, hrightFresh, hcarryFresh,
      hleftNe.1, hleftNe.2, hrightNe.1, hrightNe.2, hcarryNe.1,
      hcarryNe.2, hslots, hcrepPrimitive, assignCrepValues,
      updateCrepLocal, restoreCrepResult, restoreCrepLocal, hrestore]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_two_words structs context sourceLocals
      state.locals name leftSlot rightSlot hrel.2.1 hlookup result carryOut
      hslots hnoalias

end Flapjack
