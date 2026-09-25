import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.CrepLang
import Flapjack.Basis.Pure.MlString

/-! Parity fixture for the exact MlString-keyed `crepSem$lookup_code_def` port
(`Flapjack/Pancake/Semantics/CrepSem/LookupCode.lean`), mirroring the direct HOL
oracle `scripts/hol-probes/crep_lookup_code_probe.out` rows
`lookup_code_valid`, `lookup_code_missing`, `lookup_code_arity`, and
`lookup_code_duplicate`. -/

namespace Flapjack.Test.CrepLookupCodeHOLParity

open Flapjack

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString

private def key (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

/-- Exact code map keyed by `mlstring`, containing a well-formed `id` entry and a
duplicate-parameter `dup` entry. -/
private def exactCodeMap : CrepCodeMapExact 8 :=
  fun name =>
    if name = key "id" then some ([1], Flapjack.CrepProgHOL.skip)
    else if name = key "dup" then some ([1, 1], Flapjack.CrepProgHOL.skip)
    else none

private def word8 (n : Nat) : HolWordLab 8 := HolWordLab.word (BitVec.ofNat 8 n)

/-- Oracle row `lookup_code_valid`: success returns the body and the zipped
locals. -/
private example :
    (lookupCodeHOL exactCodeMap (key "id") [word8 7] 1).map
        (fun result => FLOOKUP result.2 1) = some (some (word8 7)) := by decide

/-- Oracle row `lookup_code_missing`. -/
private example : lookupCodeHOL exactCodeMap (key "missing") [] 0 = none := by decide

/-- Oracle row `lookup_code_arity`: declared arity differs from supplied arity. -/
private example : lookupCodeHOL exactCodeMap (key "id") [word8 7, word8 8] 2 = none := by
  decide

/-- Oracle row `lookup_code_duplicate`: duplicate declared parameters. -/
private example : lookupCodeHOL exactCodeMap (key "dup") [word8 7, word8 8] 2 = none := by
  decide

#guard
  (lookupCodeHOL exactCodeMap (key "id") [word8 7] 1).map
      (fun result => FLOOKUP result.2 1) == some (some (word8 7)) &&
    (lookupCodeHOL exactCodeMap (key "missing") [] 0).isNone &&
    (lookupCodeHOL exactCodeMap (key "id") [word8 7, word8 8] 2).isNone &&
    (lookupCodeHOL exactCodeMap (key "dup") [word8 7, word8 8] 2).isNone

/-- Kernel-checked production bridge at width 8. -/
example (code : CrepCodeMapExact 8)
    (fname : MlS) (args : List (PanWordLab (BitVec 8))) (len : Nat) :
    (lookupCodeHOL code fname (args.map PanWordLab.toHolWordLab) len).map
        (fun result => (Flapjack.crepProgOfHOL result.1, mapFiniteMap HolWordLab.toPanWordLab result.2)) =
      lookupCrepHolCode (Flapjack.codeMapExactToProd code)
        (Flapjack.Basis.Pure.MlString.toStringOfBytes fname) args len :=
  Flapjack.lookupCodeHOL_exactToProd code fname args len

/-- Kernel-checked executed-path bridge at width 8: the executed
`lookupCrepRuntimeCode` on the `codeMapExactToProd` image of an exact code map
is exactly the image of the exact `lookupCodeHOL`. -/
example (code : CrepCodeMapExact 8)
    (fname : MlS) (values : List (BitVec 8)) (len : Nat) :
    Flapjack.lookupCrepRuntimeCode (Flapjack.Basis.Pure.MlString.toStringOfBytes fname) values
        (Flapjack.codeMapExactToProd code) =
      (lookupCodeHOL code fname ((values.map PanWordLab.word).map PanWordLab.toHolWordLab) len).map
        (fun result => (Flapjack.crepProgOfHOL result.1, mapFiniteMap HolWordLab.toPanWordLab result.2)) :=
  Flapjack.lookupCrepRuntimeCode_exactImage code fname values len

end Flapjack.Test.CrepLookupCodeHOLParity
