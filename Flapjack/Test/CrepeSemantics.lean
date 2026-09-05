import Flapjack.CrepeSemantics

namespace Flapjack

/-! Small executable witnesses for every control-result constructor in the
    full Crepe evaluator. These are deliberately word-polymorphic in the
    implementation, while the regression uses Nat to keep reduction fast. -/

def crepeSemanticsState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepeSemanticsPrimitive : CrepPrimitiveHandler Nat
  | .addCarry, [left, right, carry] => some [left + right + carry, 0]
  | _, _ => none

def crepeSemanticsFfi : CrepFfiHandler Nat :=
  noCrepFfi Nat

def crepeSemanticsSharedMem : CrepSharedMemHandler Nat :=
  defaultCrepSharedMemHandler

def crepeSemanticsFunctions : List (CompiledFunction Nat) :=
  [{ name := "inc"
     params := [0]
     body := .return [.op .add [.var 0, .const 1]]
     returnShape := .one }]

def crepeSemanticsCall : CrepProg Nat :=
  .seq
    (.dec 1 (.const 41)
      (.call (some ([2], none)) "inc" [.var 1]))
    (.return [.var 2])

def crepeSemanticsLoop : CrepProg Nat :=
  .seq
    (.assign 0 (.const 3))
    (.seq
      (.while (.var 0)
        (.seq
          (.assign 0 (.op .sub [.var 0, .const 1]))
          (.ite (.cmp .equal (.var 0) (.const 0)) (.break 0) .skip)))
      (.return [.var 0]))

def crepeSemanticsHandlerFunctions : List (CompiledFunction Nat) :=
  [{ name := "raise"
     params := []
     body := .raise 7
     returnShape := .one }]

def crepeSemanticsHandlerCall : CrepProg Nat :=
  .call (some ([], some (7, .return [.const 9]))) "raise" []

def crepeSemanticsMemory : CrepProg Nat :=
  .seq
    (.store (.const 10) (.const 7))
    (.seq
      (.shMem .load 0 (.const 10))
      (.return [.var 0]))

def crepeSemanticsPrimitiveProgram : CrepProg Nat :=
  .seq
    (.assign 1 (.const 1))
    (.seq
      (.assign 2 (.const 2))
      (.seq
        (.assign 3 (.const 0))
        (.seq
          (.primitive [4, 5] .addCarry [1, 2, 3])
          (.return [.var 4]))))

theorem crepe_full_call_semantics :
    evalCrepFullResult crepeSemanticsFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsCall =
      some [42] := by
  native_decide

theorem crepe_full_loop_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 50 crepeSemanticsState crepeSemanticsLoop =
      some [0] := by
  native_decide

theorem crepe_full_handler_semantics :
    evalCrepFullResult crepeSemanticsHandlerFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsHandlerCall =
      some [9] := by
  native_decide

theorem crepe_full_memory_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsMemory =
      some [7] := by
  native_decide

theorem crepe_full_primitive_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsPrimitiveProgram =
      some [3] := by
  native_decide

end Flapjack
