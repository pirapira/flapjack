import Flapjack.Pipeline

/-!
# Pancake `get_eids` parity

The expected mappings are transcribed from
`cakeml/pancake/pan_to_crepScript.sml:346-353` (`get_eids_def`).  The test
exercises the complete observable: body traversal order, first-occurrence
deduplication, and consecutive target-word numbering.
-/

namespace Flapjack.Test.PanGetEidsParity

open Flapjack

def raiseE (exception : ExceptionId) : Prog Nat :=
  .raise exception (.const 0)

def sourceFunctions : List (FunDecl Nat) :=
  [{ name := "first", inline := false, exported := false, params := [],
      body := .seq (raiseE "E") (raiseE "F"), returnShape := .one },
   { name := "second", inline := false, exported := false, params := [],
      body := .seq (raiseE "E") (raiseE "G"), returnShape := .one }]

example : pipelineGetEids id ([] : List (FunDecl Nat)) = [] := by
  rfl

example : pipelineGetEids id sourceFunctions = [("E", 0), ("F", 1), ("G", 2)] := by
  simp [pipelineGetEids, pipelineExceptionIds, sourceFunctions, raiseE,
    expIds, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

end Flapjack.Test.PanGetEidsParity
