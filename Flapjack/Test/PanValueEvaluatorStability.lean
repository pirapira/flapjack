import Flapjack.PanValueEvaluatorStability

namespace Flapjack.Test.PanValueEvaluatorStability

open Flapjack

/-! A concrete instance of Cake's `eval_distinct_lists_not_affect'` helper:
    installing a fresh local binding does not change an expression that does
    not mention that local.  The expected value is checked independently by
    reducing the original evaluator. -/

def expression : Exp Nat := .op .add [.const 1, .const 2]

def baseLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 7) else none

theorem fresh_local_stability_fixture :
    evalPanValueExp ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 expression none = some (.word 3) := by
  calc
    evalPanValueExp ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 expression none =
        evalPanValueExp ([] : StructContext) baseLocals (fun _ => none)
          (fun _ => none) 0 0 8 expression none := by
            exact evalPanValueExp_update_local_not_mem ([] : StructContext)
              baseLocals (fun _ => none) (fun _ => none) 0 0 8 expression none
              "fresh" (.word 99) (by
                simp [expression, expLocalVars, expLocalVars.expLocalVarsList])
    _ = some (.word 3) := by
      simp [expression, evalPanValueExp, evalPanValueExp.evalPanValueExps,
        evalPanBinOp]

def fields : List (FieldName × Exp Nat) :=
  [("left", .op .add [.const 1, .const 2]), ("right", .const 4)]

def namedStructs : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

theorem fresh_field_list_stability_fixture :
    evalPanValueExp.evalPanValueFields ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 fields none =
      some [("left", .word 3), ("right", .word 4)] := by
  calc
    evalPanValueExp.evalPanValueFields ([] : StructContext)
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 fields none =
        evalPanValueExp.evalPanValueFields ([] : StructContext) baseLocals
          (fun _ => none) (fun _ => none) 0 0 8 fields none := by
            exact evalPanValueFields_update_local_not_mem ([] : StructContext)
              baseLocals (fun _ => none) (fun _ => none) 0 0 8 fields none
              "fresh" (.word 99) (by
                intro field hfield
                simp [fields] at hfield
                rcases hfield with rfl | rfl <;>
                  simp [expLocalVars, expLocalVars.expLocalVarsList])
    _ = some [("left", .word 3), ("right", .word 4)] := by
      simp [fields, evalPanValueExp, evalPanValueExp.evalPanValueFields,
        evalPanValueExp.evalPanValueExps, evalPanBinOp]

theorem fresh_named_struct_stability_fixture :
    evalPanValueExp namedStructs
        (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
        (fun _ => none) 0 0 8 (.nStruct "Pair" fields) none =
      evalPanValueExp namedStructs baseLocals (fun _ => none) (fun _ => none)
        0 0 8 (.nStruct "Pair" fields) none := by
  exact evalPanValueExp_nStruct_update_local_not_mem namedStructs baseLocals
    (fun _ => none) (fun _ => none) 0 0 8 "Pair" fields none "fresh"
    (.word 99) (by
      intro field hfield
      simp [fields] at hfield
      rcases hfield with rfl | rfl <;>
        simp [expLocalVars, expLocalVars.expLocalVarsList])

def freshBindings : List (VarName × PanValue Nat) :=
  [("fresh-left", .word 99), ("fresh-right", .word 101)]

def expressions : List (Exp Nat) :=
  [.op .add [.const 1, .const 2], .panOp .mul [.const 3, .const 4]]

theorem fresh_bindings_stability_fixture :
    evalPanValueExps ([] : StructContext)
        (updatePanValueMapList baseLocals freshBindings) (fun _ => none)
        (fun _ => none) 0 0 8 expressions none =
      some [.word 3, .word 12] := by
  calc
    evalPanValueExps ([] : StructContext)
        (updatePanValueMapList baseLocals freshBindings) (fun _ => none)
        (fun _ => none) 0 0 8 expressions none =
        evalPanValueExps ([] : StructContext) baseLocals (fun _ => none)
          (fun _ => none) 0 0 8 expressions none := by
            exact evalPanValueExps_update_locals_not_mem ([] : StructContext)
              baseLocals (fun _ => none) (fun _ => none) 0 0 8 expressions none
              freshBindings (by
                intro binding hbinding expression' hexpression'
                simp [freshBindings] at hbinding
                simp [expressions] at hexpression'
                rcases hbinding with rfl | rfl <;>
                  rcases hexpression' with rfl | rfl <;>
                    simp [expLocalVars, expLocalVars.expLocalVarsList])
    _ = some [.word 3, .word 12] := by
      simp [expressions, evalPanValueExps,
        evalPanValueExp.evalPanValueExps, evalPanValueExp, evalPanBinOp,
        evalPanOp]

def resultGuard : Bool := match evalPanValueExp ([] : StructContext)
    (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
    (fun _ => none) 0 0 8 expression none with
  | some (.word 3) => true
  | _ => false

#eval resultGuard
#guard resultGuard

end Flapjack.Test.PanValueEvaluatorStability
