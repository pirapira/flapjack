import Flapjack.Static

/-!
# `panLang$size_of_sh_with_ctxt` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_size_of_sh_with_ctxt_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:164-171`.
-/

namespace Flapjack.Test.PanLangSizeOfShWithCtxtParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:164-171 (size_of_sh_with_ctxt_def)"

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def parityGuard : Bool :=
  shapeSizeWithContext [] .one == 1 &&
  shapeSizeWithContext pairContext (.named "Pair") == 2 &&
  shapeSizeWithContext pairContext (.named "Missing") == 1 &&
  shapeSizeWithContext pairContext
      (.comb [.one, .named "Pair", .comb [.one, .one]]) == 5

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:164-171 (size_of_sh_with_ctxt_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangSizeOfShWithCtxtParity
