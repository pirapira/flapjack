import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_global_var_def`
    (`cakeml/pancake/panStaticScript.sml:625-630`).

The missing-variable case is intentionally checked through the same
location/scope-sensitive diagnostic used by Cake's `get_scope_msg_def`; this
is an intermediate static-check result, not merely an end-to-end acceptance
test.
-/

def staticGlobalVarParityContext : Context :=
  { locals := []
    globals := [("g", { shape := .one })]
    functions := []
    expectedReturn := none
    exceptions := []
    structs := []
    scope := .funScope "f" ""
    inLoop := false
    reachable := .isReach
    last := .invisLast
    location := "line: " }

#guard
  match (checkGlobalVar staticGlobalVarParityContext "g").1 with
  | .ok info => match info.shape with
    | .one => true
    | _ => false
  | .error _ => false

#guard
  staticResultErrorMessage
      (checkGlobalVar staticGlobalVarParityContext "missing") ==
    some "line: variable missing is not in scope in function f\n"

#guard
  staticResultOk
      (checkExp staticGlobalVarParityContext (.var .global "g" : Exp Nat)) &&
    staticResultErrorMessage
      (checkExp staticGlobalVarParityContext (.var .global "missing" : Exp Nat)) ==
      some "line: variable missing is not in scope in function f\n"

/-! Direct executable parity for CakeML's `check_local_var_def`
    (`panStaticScript.sml:633-638`). -/

def staticLocalVarParityContext : Context :=
  { staticGlobalVarParityContext with
    locals := [("x", { shapedBased := .word .trusted })] }

#guard
  match (checkLocalVar staticLocalVarParityContext "x").1 with
  | .ok info => match info.shapedBased with
    | .word .trusted => true
    | _ => false
  | .error _ => false

#guard
  staticResultErrorMessage
      (checkLocalVar staticLocalVarParityContext "missing") ==
    some "line: variable missing is not in scope in function f\n"

#guard
  staticResultOk
      (checkExp staticLocalVarParityContext (.var .local "x" : Exp Nat)) &&
    staticResultErrorMessage
      (checkExp staticLocalVarParityContext (.var .local "missing" : Exp Nat)) ==
      some "line: variable missing is not in scope in function f\n"

end Flapjack
