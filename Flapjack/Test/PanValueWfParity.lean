import Flapjack.PanValues

namespace Flapjack.Test.PanValueWfParity

open Flapjack

/-! Direct parity for the ported Cake value-level well-formedness predicate
    `is_wf_shape_v` (`panPropsScript.sml:24`) and its shape bridge
    `is_wf_shape_of_v` (`:38`). -/

def namedContext : StructContext :=
  [("S", { fields := [], size := 1 })]

def wordValue : PanValue Nat := .word 3

def recordValue : PanValue Nat := .rStruct [.word 1, .word 2]

def namedValue : PanValue Nat := .nStruct "S" []

def unknownNamedValue : PanValue Nat := .nStruct "T" []

theorem panValueIsWf_word : panValueIsWf ([] : StructContext) wordValue = true := by
  simp [panValueIsWf, wordValue]

theorem panValueIsWf_record : panValueIsWf ([] : StructContext) recordValue = true := by
  simp [panValueIsWf, panValueIsWfValues, recordValue]

theorem panValueIsWf_named : panValueIsWf namedContext namedValue = true := by
  simp [panValueIsWf, panValueIsWfFields, namedContext, namedValue, lookupInfo]

def parityGuard : Bool :=
  panValueIsWf ([] : StructContext) wordValue &&
  panValueIsWf ([] : StructContext) recordValue &&
  panValueIsWf namedContext namedValue &&
  !panValueIsWf namedContext unknownNamedValue &&
  isWfShape ([] : StructContext) (panValueShape ([] : StructContext) wordValue) &&
  isWfShape ([] : StructContext) (panValueShape ([] : StructContext) recordValue) &&
  isWfShape namedContext (panValueShape namedContext namedValue)

#eval parityGuard
#guard parityGuard

theorem panValueIsWf_isWfShape_panValueShape_fixture :
    isWfShape namedContext (panValueShape namedContext namedValue) = true :=
  panValueIsWf_isWfShape_panValueShape namedContext namedValue
    (by simp [panValueIsWf, panValueIsWfFields, namedContext, namedValue,
      lookupInfo])

/-! `is_wf_shape_v_drop` (`panPropsScript.sml:63`): dropping a prefix of the
    context preserves value well-formedness. -/

def dropContext : StructContext :=
  [("T", { fields := [], size := 1 }), ("S", { fields := [], size := 1 })]

theorem panValueIsWf_of_drop_fixture :
    panValueIsWf dropContext namedValue = true :=
  panValueIsWf_of_drop dropContext namedValue 1 (by
    simp [panValueIsWf, panValueIsWfFields, dropContext, namedValue, lookupInfo])

def dropGuard : Bool :=
  panValueIsWf (dropContext.drop 1) namedValue &&
  panValueIsWf dropContext namedValue

#eval dropGuard
#guard dropGuard

/-! `is_wf_shape_v_nil` (`panPropsScript.sml:56`): at the empty struct context,
    value well-formedness coincides with shape well-formedness. -/

theorem panValueIsWf_eq_isWfShape_panValueShape_of_nil_fixture :
    isWfShape ([] : StructContext)
        (panValueShape ([] : StructContext) namedValue) =
      panValueIsWf ([] : StructContext) namedValue :=
  panValueIsWf_eq_isWfShape_panValueShape_of_nil ([] : StructContext) namedValue
    rfl

theorem panValueIsWf_of_isWfShape_panValueShape_nil_fixture :
    panValueIsWf ([] : StructContext) recordValue = true :=
  panValueIsWf_of_isWfShape_panValueShape_nil recordValue (by
    simp [panValueShape, isWfShape, isWfShape.isWfShapeList, recordValue])

def nilGuard : Bool :=
  (isWfShape ([] : StructContext)
      (panValueShape ([] : StructContext) wordValue) ==
    panValueIsWf ([] : StructContext) wordValue) &&
  (isWfShape ([] : StructContext)
      (panValueShape ([] : StructContext) recordValue) ==
    panValueIsWf ([] : StructContext) recordValue)

#eval nilGuard
#guard nilGuard

/-! `mem_load_is_wf_shape_v` (`panPropsScript.sml:90`): the flat memory load
    returns well-formed values. -/

def flatMemory : Nat → Option (PanValue Nat) := fun _ => some (.word 5)

def flatLoadGuard : Bool :=
  match panValueFlatLoad ([] : StructContext) flatMemory 8 100 (.comb [.one]) with
  | some value => panValueIsWf ([] : StructContext) value
  | none => false

#eval flatLoadGuard
#guard flatLoadGuard

theorem panValueFlatLoad_wf_fixture :
    panValueIsWf ([] : StructContext) (.word 5) = true :=
  panValueFlatLoad_wf ([] : StructContext) flatMemory 8 100 .one none (.word 5) (by
    simp [panValueFlatLoad, isWfShape, panValueFlatLoadFuel, panValueFlatReadWord,
      panValueFlatContextFuel, panValueFlatShapeFuel, flatMemory])

example : True := by
  match h : panValueFlatLoad ([] : StructContext) flatMemory 8 100 .one with
  | some value =>
      have _ := panValueFlatLoad_wf ([] : StructContext) flatMemory 8 100 .one none value h
      trivial
  | none => trivial

/-! `eval_is_wf_shape_v` (`panPropsScript.sml:126`): evaluation preserves
    value well-formedness, given well-formed local and global stores. -/

def evalWfLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 7) else none

def evalWfGlobals : VarName → Option (PanValue Nat) := fun _ => none

def evalWfMemory : Nat → Option (PanValue Nat) := fun _ => none

def evalWfGuard : Bool :=
  match evalPanValueExp ([] : StructContext) evalWfLocals evalWfGlobals
      evalWfMemory 0 0 8 (.op .add [.var .local "x", .const 1]) with
  | some value => panValueIsWf ([] : StructContext) value
  | none => false

#eval evalWfGuard
#guard evalWfGuard

example : True := by
  match h : evalPanValueExp ([] : StructContext) evalWfLocals evalWfGlobals
      evalWfMemory 0 0 8 (.op .add [.var .local "x", .const 1]) with
  | some value =>
      have _ := evalPanValueExp_isWfShape ([] : StructContext) evalWfLocals
        evalWfGlobals evalWfMemory 0 0 8
        (fun name value hname => by
          by_cases hx : (name == "x") = true
          · simp [evalWfLocals, hx] at hname
            subst hname
            simp [panValueIsWf]
          · simp [evalWfLocals, hx] at hname)
        (fun name value hname => by simp [evalWfGlobals] at hname)
        (.op .add [.var .local "x", .const 1]) none value h
      trivial
  | none => trivial

end Flapjack.Test.PanValueWfParity
