import Flapjack.Pancake.PanStatic

namespace Flapjack

/-! Direct executable parity for CakeML's `check_redec_var_def`
    (`cakeml/pancake/panStaticScript.sml:641-647`).  The helper checks both
    local and global namespaces and logs, rather than rejects, a redeclaration.
-/

def staticRedecVarParityContext : Context :=
  { locals := [("x", { shapedBased := .word .trusted })]
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

#guard staticResultOk (checkRedecVar staticRedecVarParityContext "fresh")
#guard (checkRedecVar staticRedecVarParityContext "fresh").2.isEmpty

#guard
  (checkRedecVar staticRedecVarParityContext "x").2.map statErrMessage ==
    ["line: variable x is redeclared in function f\n"]

#guard
  (checkRedecVar staticRedecVarParityContext "g").2.map statErrMessage ==
    ["line: variable g is redeclared in function f\n"]

end Flapjack
