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

def resultGuard : Bool := match evalPanValueExp ([] : StructContext)
    (updatePanValueMap baseLocals "fresh" (.word 99)) (fun _ => none)
    (fun _ => none) 0 0 8 expression none with
  | some (.word 3) => true
  | _ => false

#eval resultGuard
#guard resultGuard

end Flapjack.Test.PanValueEvaluatorStability
