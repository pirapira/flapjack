import Flapjack.PanGlobals

/-!
# Pancake `exceptions` parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_exceptions_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:328-337`.
-/

namespace Flapjack.Test.PanLangExceptionsParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:328-337 (exceptions_def)"

def exceptionDeclaration : Decl Nat := .exnDecl "E" (.comb [.one, .one])

def parityGuard : Bool :=
  (match exceptionEntries ([] : List (Decl Nat)) with
  | [] => true
  | _ => false) &&
  (match exceptionEntries [exceptionDeclaration] with
  | [("E", .comb [.one, .one])] => true
  | _ => false)

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:328-337 (exceptions_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangExceptionsParity
