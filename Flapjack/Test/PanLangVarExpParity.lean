import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Exp

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

/-! ## Exact-carrier parity (`var_exp` over the exact `ExpHOL`) -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Exact `MlS` name (HOL `mlstring`) for the probe's `«x»`. -/
def xName : MlS := ofString "x"

def yName : MlS := ofString "y"

/-- The exact `ExpHOL` image of `nested`, with `MlS` names. -/
def nestedHOL : ExpHOL 8 :=
  .rstruct [.var .local xName, .var .global (ofString "g"),
    .nstruct (ofString "S") [(ofString "field", .var .local yName)],
    .load .one (.var .global (ofString "addr"))]

#guard (varExpHOL (.var .local xName : ExpHOL 8)) == [xName]
#guard varExpHOL nestedHOL == [xName, yName]

example : varExpHOL (.var .local xName : ExpHOL 8) = [xName] := by
  simp [varExpHOL]

example : varExpHOL nestedHOL = [xName, yName] := by
  simp [varExpHOL, nestedHOL]

/-! ## `global_var_exp` specified-fragment parity over the exact `ExpHOL`

HOL's `global_var_exp_def` is partial: `Load32`, `BaseAddr`, `TopAddr` and
`BytesInWord` are `ARB`, so `globalVarExpHOL` is untagged and extends the
specification there.  The oracle rows below cover the specified fragment. -/

#guard (globalVarExpHOL (.var .global (ofString "g") : ExpHOL 8)) == [ofString "g"]
#guard globalVarExpHOL nestedHOL == [ofString "g", ofString "addr"]

example : globalVarExpHOL (.var .global (ofString "g") : ExpHOL 8) = [ofString "g"] := by
  simp [globalVarExpHOL]

example : globalVarExpHOL nestedHOL = [ofString "g", ofString "addr"] := by
  simp [globalVarExpHOL, nestedHOL]

/-! ## `global_var_exp` Option-valued specification parity

`globalVarExpHOL?` is the precise partial rendering: it returns `none` exactly
on the four HOL `ARB` constructors and `some` of the HOL clause result on the
thirteen specified clauses. -/

#guard (globalVarExpHOL? (.var .global (ofString "g") : ExpHOL 8)) ==
  some [ofString "g"]
#guard globalVarExpHOL? nestedHOL == some [ofString "g", ofString "addr"]
#guard (globalVarExpHOL? (.load32 (.var .local xName) : ExpHOL 8)) ==
  (none : Option (List MlS))
#guard (globalVarExpHOL? (.baseAddr : ExpHOL 8)) == (none : Option (List MlS))
#guard (globalVarExpHOL? (.topAddr : ExpHOL 8)) == (none : Option (List MlS))
#guard (globalVarExpHOL? (.bytesInWord : ExpHOL 8)) == (none : Option (List MlS))

example : globalVarExpHOL? (.var .global (ofString "g") : ExpHOL 8) =
    some [ofString "g"] := by
  simp

example : globalVarExpHOL? nestedHOL = some [ofString "g", ofString "addr"] := by
  simp [nestedHOL]

example : (globalVarExpHOL? (.load32 (.var .local xName) : ExpHOL 8)) = none := by
  simp

end Flapjack.Test.PanLangVarExpParity
