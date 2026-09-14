import Flapjack.Language

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

end Flapjack.Test.PanLangFunIdsParity
