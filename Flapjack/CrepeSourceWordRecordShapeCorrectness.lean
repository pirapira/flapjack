import Flapjack.CrepeSourceWordRecordCorrectness
import Flapjack.CrepeNestedDecsStability

/-!
Generic state-relation support for a structured record containing an arbitrary
list of scalar word values.  This is the local-state bridge needed by the
general declaration and assignment correctness constructors.
-/

namespace Flapjack

theorem panShapeMatches_rStruct_word_list
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (values : List α) :
    panShapeMatches
      (panValueShape structs (.rStruct (values.map (fun value => .word value))))
      (.comb (values.map (fun _ => .one))) = true := by
  have hlist : ∀ wordList : List α,
      panShapeMatches.panShapeListMatches
        (wordList.map (fun _ => .one))
        (wordList.map (fun _ => .one)) = true := by
    intro wordList
    induction wordList with
    | nil => simp [panShapeMatches.panShapeListMatches]
    | cons word wordList ih =>
        simp [panShapeMatches.panShapeListMatches, ih, panShapeMatches]
  simpa [panValueShape, Function.comp_def, panShapeMatches] using
    hlist values

theorem panValueCrepLocalsRel_update_word_list
    [OfNat α 0]
    [BEq α] [LawfulBEq α]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (slots : List Nat) (values : List α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots))
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    panValueCrepLocalsRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct (values.map (fun value => .word value))))
      (updateCrepLocalList crepLocals slots values) := by
  intro current currentValue currentShape currentSlots hcurrent hcurrentLookup
  by_cases hname : current = name
  · subst current
    have hpair :
        (.comb (values.map (fun _ => .one)), slots) =
          (currentShape, currentSlots) := by
      have hlookup' :
          some (.comb (values.map (fun _ => .one)), slots) =
            some (currentShape, currentSlots) := by
        simpa [hlookup] using hcurrentLookup
      exact Option.some.inj hlookup'
    have hshape : currentShape =
        .comb (values.map (fun _ => .one)) :=
      (congrArg Prod.fst hpair).symm
    have hslots : currentSlots = slots :=
      (congrArg Prod.snd hpair).symm
    cases hshape
    cases hslots
    have hvalue : currentValue =
        .rStruct (values.map (fun value => .word value)) := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    constructor
    · exact panShapeMatches_rStruct_word_list structs values
    · have hread := readCrepLocals_updateCrepLocalList crepLocals slots
        values hlength hdistinct
      simpa [panValueFlatWords_rStruct_word_list] using hread
  · have hcurrentOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hname] using hcurrent
    have hold := hrel current currentValue currentShape currentSlots
      hcurrentOld hcurrentLookup
    have hnotOld : ∀ slot ∈ slots, slot ∉ currentSlots := by
      intro slot hslot
      exact hnoalias current currentShape currentSlots hname
        hcurrentLookup slot hslot
    have hreadSame :=
      readCrepLocals_updateCrepLocalList_of_not_mem crepLocals slots values
        currentSlots hlength hnotOld
    exact ⟨hold.1, hreadSame.trans hold.2⟩

end Flapjack
