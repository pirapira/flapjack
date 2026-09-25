import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl

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

/-! Exact-carrier parity: `exceptionsHOL` over the faithful `DeclHOL` carrier
replays the same HOL-EVAL rows. -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def exceptionDeclHOL : DeclHOL 8 :=
  .exnDecl (ofString "E") (.comb [.one, .one])

#guard (exceptionsHOL ([] : List (DeclHOL 8))).length == 0
#guard (exceptionsHOL [exceptionDeclHOL]).length == 1

/-- HOL-EVAL oracle row `empty=[]`. -/
example : exceptionsHOL ([] : List (DeclHOL 8)) = [] := rfl

/-- HOL-EVAL oracle row `exception=[(«E»,Comb [One; One])]`. -/
example : exceptionsHOL [exceptionDeclHOL] =
    [(ofString "E", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one])] := rfl

end Flapjack.Test.PanLangExceptionsParity
