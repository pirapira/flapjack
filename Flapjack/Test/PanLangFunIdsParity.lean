import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Prog

/-!
# Pancake `fun_ids` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_fun_ids_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:336-349`.
-/

namespace Flapjack.Test.PanLangFunIdsParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:336-349 (fun_ids_def)"

def handler : Prog Nat :=
  .call none "g" []

def call : Prog Nat :=
  .call (some (none, some ("E", "h", handler))) "f" []

def declarationCall : Prog Nat :=
  .decCall "x" .one "d" [] handler

def parityGuard : Bool :=
  funIds (.skip : Prog Nat) == [] &&
  funIds (.call none "f" [] : Prog Nat) == ["f"] &&
  funIds call == ["f", "g"] &&
  funIds declarationCall == ["d", "g"]

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:336-349 (fun_ids_def)"
#eval parityGuard
#guard parityGuard

/-! ## Exact-carrier parity for `fun_ids` (bead flapjack-4ac.1.45)

`funIdsHOL` is the tagged port of `cakeml/pancake/panLangScript.sml:336-343`
over the exact `ProgHOL` carrier.  The guards below replay the four
`pan_lang_fun_ids_probe.out` rows through the name bridge `toStringOfBytes`. -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def fEmpty : ProgHOL 8 := .skip
def fHandler : ProgHOL 8 := .call none (ofString "g") []
def fCall : ProgHOL 8 :=
  .call (some (none, some (ofString "E", ofString "h", fHandler))) (ofString "f") []
def fDeclarationCall : ProgHOL 8 :=
  .decCall (ofString "x") .one (ofString "d") [] fHandler

def namesOf (program : ProgHOL 8) : List String :=
  (funIdsHOL program).map toStringOfBytes

#guard namesOf fEmpty == []
#guard namesOf (.call none (ofString "f") [] : ProgHOL 8) == ["f"]
#guard namesOf fCall == ["f", "g"]
#guard namesOf fDeclarationCall == ["d", "g"]

example : namesOf fCall = ["f", "g"] := by
  simp only [namesOf, fCall, fHandler, funIdsHOL, List.map_cons, List.map_nil]
  rw [toStringOfBytes_ofString_of_bytes "f" (by decide),
    toStringOfBytes_ofString_of_bytes "g" (by decide)]

example : namesOf fDeclarationCall = ["d", "g"] := by
  simp only [namesOf, fDeclarationCall, fHandler, funIdsHOL, List.map_cons,
    List.map_nil]
  rw [toStringOfBytes_ofString_of_bytes "d" (by decide),
    toStringOfBytes_ofString_of_bytes "g" (by decide)]

end Flapjack.Test.PanLangFunIdsParity
