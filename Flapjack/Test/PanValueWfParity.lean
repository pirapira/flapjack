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

/-! `eval_some_var_exp_local_lookup` (`panPropsScript.sml:621`): a successfully
    evaluated expression has all of its free local variables bound. -/

def varLookupLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 3) else none

theorem evalPanValueExp_isSome_local_fixture :
    ∃ w, varLookupLocals "x" = some w :=
  evalPanValueExp_isSome_local ([] : StructContext) varLookupLocals (fun _ => none)
    (fun _ => none) 0 0 8 (.var .local "x") none (.word 3)
    (by simp [evalPanValueExp, varLookupLocals])
    (by simp [expLocalVars])

def varLookupGuard : Bool :=
  match evalPanValueExp ([] : StructContext) varLookupLocals (fun _ => none)
      (fun _ => none) 0 0 8 (.var .local "x") none with
  | some _ => (varLookupLocals "x").isSome
  | none => false

#eval varLookupGuard
#guard varLookupGuard

/-! `mem_load_some_shape_eq` (`panPropsScript.sml:212`): a successful flat load
    returns a value of exactly the requested shape. -/

theorem panValueFlatLoad_shape_fixture :
    panValueShape ([] : StructContext) (.word 5) = .one :=
  panValueFlatLoad_shape ([] : StructContext) flatMemory 8 100 .one none (.word 5)
    (by simp [panValueFlatLoad, isWfShape, panValueFlatLoadFuel, panValueFlatReadWord,
      panValueFlatContextFuel, panValueFlatShapeFuel, flatMemory])

def flatLoadShapeGuard : Bool :=
  match panValueFlatLoad ([] : StructContext) flatMemory 8 100 .one with
  | some value =>
      (match panValueShape ([] : StructContext) value with | .one => true | _ => false)
  | none => false

#eval flatLoadShapeGuard
#guard flatLoadShapeGuard

/-! Cake's `mem_loads_some_shape_eq` (`panPropsScript.sml:194`): the list and
    fields flat loads return values whose shapes are exactly the requested ones. -/

def flatLoadListGuard : Bool :=
  match panValueFlatLoadList ([] : StructContext) flatMemory 8 100 [.one] with
  | some values =>
      (match values.map (panValueShape ([] : StructContext)) with
       | [.one] => true
       | _ => false)
  | none => false

def flatLoadFieldsGuard : Bool :=
  match panValueFlatLoadFields ([] : StructContext) flatMemory 8 100 [("f", .one)] with
  | some values =>
      (match values.map (fun field => panValueShape ([] : StructContext) field.2) with
       | [.one] => true
       | _ => false)
  | none => false

#eval flatLoadListGuard
#guard flatLoadListGuard
#eval flatLoadFieldsGuard
#guard flatLoadFieldsGuard

example : True := by
  match h : panValueFlatLoadList ([] : StructContext) flatMemory 8 100 [.one] with
  | some values =>
      have _ := panValueFlatLoadList_shape ([] : StructContext) flatMemory 8 100 [.one]
        none values h
      trivial
  | none => trivial
/-! `evaluate_replicate_const` (`pan_to_crepProofScript.sml:3051`): evaluating a
    list of zero constants always succeeds, producing the same number of zero
    words. -/

theorem evalPanValueExps_replicate_const_fixture :
    (List.replicate 3 (.const (0 : Nat))).mapM
        (fun expression => evalPanValueExp ([] : StructContext) (fun _ => none)
          (fun _ => none) (fun _ => none) 0 0 8 expression) =
      some (List.replicate 3 (.word (0 : Nat))) :=
  evalPanValueExps_replicate_const ([] : StructContext) (fun _ => none)
    (fun _ => none) (fun _ => none) 0 0 8 3

#check @evalPanValueExps_replicate_const

/-! `shape_val` / `shape_vals` (`panLangScript.sml:190`) and their companion
    `eval_shape_val_NONE` / `eval_shape_val_thm`
    (`pan_globalsProofScript.sml:968`, `:980`). -/

theorem shapeVal_shape_fixture :
    panValueShape ([] : StructContext) (.word 0) = .one :=
  shapeVal_shape ([] : StructContext) (fun _ => none) (fun _ => none)
    (fun _ => none) 0 0 8 none .one (by simp [isWfShape]) (.word 0)
    (by simp [shapeVal, evalPanValueExp])

theorem shapeVal_isSome_fixture :
    (evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none)
      (fun _ => none) 0 0 8 (shapeVal (.comb [.one])) none).isSome = true :=
  shapeVal_isSome ([] : StructContext) (fun _ => none) (fun _ => none)
    (fun _ => none) 0 0 8 none (.comb [.one])

def shapeValGuard : Bool :=
  match evalPanValueExp ([] : StructContext) (fun _ => none) (fun _ => none)
      (fun _ => none) 0 0 8 (shapeVal (.comb [.one, .one])) none with
  | some value =>
      (match panValueShape ([] : StructContext) value with
       | .comb [.one, .one] => true
       | _ => false)
  | none => false

#eval shapeValGuard
#guard shapeValGuard

/-! `opt_mmap_eval_is_wf_shape_v` (`pan_to_crepProofScript.sml:2328`): a
    successful evaluator list preserves well-formedness for constants and
    source-local values alike. -/

def evaluatorLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 9) else none

theorem evalPanValueExps_isWfShape_fixture :
    panValueIsWfValues ([] : StructContext)
        [.word 7, .word 9] = true := by
  apply evalPanValueExps_isWfShape ([] : StructContext) evaluatorLocals
    (fun _ => none) (fun _ => none) 0 0 8
    (expressions := [.const 7, .var .local "x"])
    (memoryAccess := none) (values := [.word 7, .word 9])
  · intro name value hvalue
    simp [evaluatorLocals] at hvalue
    rcases hvalue with ⟨rfl, rfl⟩
    simp [panValueIsWf]
  · simp
  · simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
      evalPanValueExp, evaluatorLocals]

#check @evalPanValueExps_isWfShape

end Flapjack.Test.PanValueWfParity
