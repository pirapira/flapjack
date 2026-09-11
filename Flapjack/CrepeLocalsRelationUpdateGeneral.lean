import Flapjack.CrepeNestedDecsStability
import Flapjack.CrepeStateRelation

/-!
Generic local-state transition for a shape-preserving assignment.  The
source binding may contain any supported structured value; the target update
receives its flattened words in the slots recorded by the compile context.
-/

namespace Flapjack

theorem panValueCrepLocalsRel_update_value
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals : VarName → Option (PanValue α))
    (crepLocals : Nat → Option α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α) (values : List α)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : lookupInfo name context.vars = some (shape, slots))
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hflat : panValueFlatWords value = values)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    panValueCrepLocalsRel structs context
      (updatePanValueMap sourceLocals name value)
      (updateCrepLocalList crepLocals slots values) := by
  intro current currentValue currentShape currentSlots hcurrent hcurrentLookup
  by_cases hname : current = name
  · subst current
    have hpair : (shape, slots) = (currentShape, currentSlots) := by
      have hlookup' : some (shape, slots) =
          some (currentShape, currentSlots) := by
        simpa [hlookup] using hcurrentLookup
      exact Option.some.inj hlookup'
    have hshape' : currentShape = shape :=
      (congrArg Prod.fst hpair).symm
    have hslots : currentSlots = slots :=
      (congrArg Prod.snd hpair).symm
    cases hshape'
    cases hslots
    have hvalue : currentValue = value := by
      rw [updatePanValueMap] at hcurrent
      simpa using hcurrent.symm
    cases hvalue
    have hread := readCrepLocals_updateCrepLocalList crepLocals slots values
      hlength hdistinct
    simpa [hflat] using And.intro hshape hread
  · have hcurrentOld : sourceLocals current = some currentValue := by
      rw [updatePanValueMap] at hcurrent
      simpa [hname] using hcurrent
    have hold := hrel current currentValue currentShape currentSlots
      hcurrentOld hcurrentLookup
    have hnotOld : ∀ slot ∈ slots, slot ∉ currentSlots :=
      hnoalias current currentShape currentSlots hname hcurrentLookup
    have hreadSame :=
      readCrepLocals_updateCrepLocalList_of_not_mem crepLocals slots values
        currentSlots hlength hnotOld
    exact ⟨hold.1, hreadSame.trans hold.2⟩

end Flapjack
