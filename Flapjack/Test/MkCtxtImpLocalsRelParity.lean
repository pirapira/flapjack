import Flapjack.Pancake.Proofs.PanToCrep

/-!
Parity check for the source-shaped port of HOL `mk_ctxt_imp_locals_rel`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4677`) as
`Flapjack.mkCtxtImpLocalsRel`: the initial compiler context (empty variable
map, slot bound zero, function table from `make_funcs`) satisfies `locals_rel`
against the empty source locals map and any target locals. The Lean statement
uses the production `String`/`Shape`/`Decl` carriers, so the withdrawn tag stays
off and the exact MlString replacement is tracked by `flapjack-pxn.18.3.5.8`.
-/

namespace Flapjack.Test.MkCtxtImpLocalsRelParity

open Flapjack

/-- The initial proof context mirrors Cake `mk_ctxt FEMPTY (make_funcs pc) 0 es`. -/
def initialContext (declarations : List (Decl Nat)) : PanToCrepProofContext Nat :=
  { vars := (FEMPTY : FiniteMap String (Shape × List Nat))
    funcs := infoMapToFiniteMap (panToCrepMakeFuncs declarations)
    eids := FEMPTY
    vmax := 0 }

example : localsRel (initialContext ([] : List (Decl Nat))) FEMPTY FEMPTY :=
  mkCtxtImpLocalsRel ([] : List (Decl Nat)) FEMPTY FEMPTY

example (locals : FiniteMap Nat (PanWordLab Nat)) :
    localsRel (initialContext ([] : List (Decl Nat))) FEMPTY locals :=
  mkCtxtImpLocalsRel ([] : List (Decl Nat)) FEMPTY locals

def runChecks : IO Bool := do
  IO.println "PASS Crep mk_ctxt initial context satisfies locals_rel"
  return true

end Flapjack.Test.MkCtxtImpLocalsRelParity