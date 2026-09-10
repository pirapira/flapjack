import Flapjack.CrepeSourceWordRecordCorrectness
import Flapjack.CrepeAssignmentCorrectness

/-!
The structured assignment boundary for a two-word record.

This packages the existing evaluator equation with the source-to-Crep local
relation, so it can be used as a state-threading case in the Pancake
correctness induction.
-/

namespace Flapjack

theorem panValueCrepLocalsRel_update_record_two_words
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (slotLeft slotRight : Nat) (left right : α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : lookupInfo name context.vars =
      some (.comb [.one, .one], [slotLeft, slotRight]))
    (hdistinct : slotLeft ≠ slotRight)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slotLeft ∉ oldSlots ∧ slotRight ∉ oldSlots) :
    panValueCrepLocalsRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct [.word left, .word right]))
      (updateCrepLocal (updateCrepLocal crepLocals slotLeft left)
        slotRight right) := by
  intro current currentValue currentShape currentSlots hcurrent hcurrentLookup
  by_cases hname : current = name
  · subst current
    have hpair : (Shape.comb [.one, .one], [slotLeft, slotRight]) =
        (currentShape, currentSlots) := by
      have hlookup' : some (Shape.comb [.one, .one], [slotLeft, slotRight]) =
          some (currentShape, currentSlots) := by
        simpa [hlookup] using hcurrentLookup
      exact Option.some.inj hlookup'
    have hshape : currentShape = Shape.comb [.one, .one] :=
      (congrArg Prod.fst hpair).symm
    have hslots : currentSlots = [slotLeft, slotRight] :=
      (congrArg Prod.snd hpair).symm
    cases hshape
    cases hslots
    have hvalue : currentValue = PanValue.rStruct [.word left, .word right] := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    constructor
    · simp [panValueShape, panShapeMatches,
        panShapeMatches.panShapeListMatches]
    · simp [readCrepLocals, updateCrepLocal, hdistinct,
        panValueFlatWords, panValueFlatWordsFuel, panValueFlatValueFuel,
        panValueFlatWordsFuel.panValueFlatWordsListFuel,
        panValueFlatValueFuel.panValueFlatValueListFuel]
  · have hcurrentOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hname] using hcurrent
    have hold := hrel current currentValue currentShape currentSlots
      hcurrentOld hcurrentLookup
    have hnotLeft : slotLeft ∉ currentSlots :=
      (hnoalias current currentShape currentSlots hname hcurrentLookup).1
    have hnotRight : slotRight ∉ currentSlots :=
      (hnoalias current currentShape currentSlots hname hcurrentLookup).2
    have hleft := readCrepLocals_update_of_not_mem crepLocals slotLeft left
      currentSlots hnotLeft
    have hright := readCrepLocals_update_of_not_mem
      (updateCrepLocal crepLocals slotLeft left) slotRight right
      currentSlots hnotRight
    exact ⟨hold.1, by
      rw [hright, hleft]
      exact hold.2⟩

theorem compile_full_pan_value_local_assign_record_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slotLeft slotRight : Nat)
    (oldLeft oldRight left right : α)
    (hlookup : lookupInfo name context.vars =
      some (.comb [.one, .one], [slotLeft, slotRight]))
    (hdistinct : slotLeft ≠ slotRight)
    (hlocals : sourceLocals name =
      some (.rStruct [.word oldLeft, .word oldRight]))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slotLeft ∉ oldSlots ∧ slotRight ∉ oldSlots) :
    evalCrepFullResult [] primitive ffi sharedMem baseAddress topAddress 30 state
        (compileProg context
          (.seq (.assign .local name
              (.rStruct [.const left, .const right]))
            (.return (.var .local name)))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        sourceLocals sourceGlobals (fun address =>
          (state.memory address).map PanValue.word)
        (.seq (.assign .local name
            (.rStruct [.const left, .const right]))
          (.return (.var .local name)))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct [.word left, .word right])) sourceGlobals sourceMemory
      { state with locals :=
          (updateCrepLocal (updateCrepLocal state.locals slotLeft left)
            slotRight right) } := by
  constructor
  · exact compile_full_pan_value_local_assign_record_return_correct
      context structs sourceLocals sourceGlobals state primitive ffi sharedMem
      baseAddress topAddress bytesInWord name slotLeft slotRight
      oldLeft oldRight left right hlookup hdistinct hlocals
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_record_two_words structs context
      sourceLocals state.locals name slotLeft slotRight left right hrel.2.1
      hlookup hdistinct hnoalias

end Flapjack
