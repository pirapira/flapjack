import Flapjack.Language

/-!
# Pancake local/global expression-variable parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_var_exp_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:253-293`.
-/

namespace Flapjack.Test.PanLangVarExpParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:253-293 (var_exp/global_var_exp)"

def nested : Exp Nat :=
  .rStruct [.var .local "x",
    .var .global "g",
    .nStruct "S" [("field", .var .local "y")],
    .load .one (.var .global "addr")]

def parityGuard : Bool :=
  expLocalVars (.var .local "x" : Exp Nat) == ["x"] &&
  expGlobalVars (.var .global "g" : Exp Nat) == ["g"] &&
  expLocalVars nested == ["x", "y"] &&
  expGlobalVars nested == ["g", "addr"]

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:253-293 (var_exp/global_var_exp)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangVarExpParity
