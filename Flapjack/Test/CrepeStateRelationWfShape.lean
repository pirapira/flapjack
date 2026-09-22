import Flapjack.CrepeNestedDecsStability

namespace Flapjack.Test.CrepeStateRelationWfShape

open Flapjack

def context : CompileContext Nat :=
  { vars := [("x", (.one, [0]))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 8 }

def sourceLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 7) else none

def crepLocals : Nat → Option Nat :=
  fun slot => if slot == 0 then some 7 else none

theorem locals_rel_wf_shape_fixture :
    panShapeMatches (panValueShape ([] : StructContext) (.word 7)) .one = true ∧
      isWfShape ([] : StructContext)
        (panValueShape ([] : StructContext) (.word 7)) = true := by
  apply panValueCrepLocalsRel_wf_shape ([] : StructContext) context sourceLocals
    crepLocals "x" (.word 7) .one [0]
  · intro name value shape slots hsource hlookup
    simp [sourceLocals] at hsource
    rcases hsource with ⟨rfl, rfl⟩
    have hshape : .one = shape ∧ [0] = slots := by
      simpa [context, lookupInfo] using hlookup
    rcases hshape with ⟨rfl, rfl⟩
    simp [crepLocals, readCrepLocals,
      panValueFlatWords, panValueFlatWordsFuel, panShapeMatches,
      panValueShape]
  · simp [sourceLocals]
  · simp [context, lookupInfo]
  · simp [panValueIsWf]

theorem locals_rel_update_fresh_slot_fixture :
    panValueCrepLocalsRel ([] : StructContext) context sourceLocals
      (updateCrepLocal crepLocals 2 99) := by
  apply panValueCrepLocalsRel_update_fresh_slot
    ([] : StructContext) context sourceLocals crepLocals 2 99
  · intro name value shape slots hsource hlookup
    simp [sourceLocals] at hsource
    rcases hsource with ⟨rfl, rfl⟩
    have hshape : .one = shape ∧ [0] = slots := by
      simpa [context, lookupInfo] using hlookup
    rcases hshape with ⟨rfl, rfl⟩
    simp [crepLocals, readCrepLocals,
      panValueFlatWords, panValueFlatWordsFuel, panShapeMatches,
      panValueShape]
  · simp [context]
  · intro name shape slots hlookup current hcurrent
    have hshape : "x" = name ∧ .one = shape ∧ [0] = slots := by
      simpa [context, lookupInfo] using hlookup
    rcases hshape with ⟨rfl, rfl, rfl⟩
    simp at hcurrent
    omega

end Flapjack.Test.CrepeStateRelationWfShape
