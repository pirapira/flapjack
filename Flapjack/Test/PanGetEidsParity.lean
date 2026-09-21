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

example : ∃ code, lookupInfo "E"
    (crepGetEidsFromDecls id [.exnDecl "E" .one, .decl .one "x" (.const 0)]) =
      some code := by
  exact crepGetEidsFromDecls_lookup_of_exception id 0
    [.exnDecl "E" .one, .decl .one "x" (.const 0)] "E" .one (by simp [exceptionEntries])

/-! The declaration-side table cardinality is the source `size_of_eids`
    cardinality used by Cake's exception-relation proof. -/
example :
    (crepGetEidsFromDecls id
      [.exnDecl "E" .one, .decl .one "x" (.const 0), .exnDecl "F" .one]).length =
      sizeOfEids
        [.exnDecl "E" .one, .decl .one "x" (.const 0), .exnDecl "F" .one] := by
  exact crepGetEidsFromDecls_length id _

/-! Cake's `get_eids_pan_simp_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:105`): simplifying the
    function bodies does not change the exception-code table, hence not its
    finite domain. -/

def getEidsDecls : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "F" (.const 0), returnShape := .one },
   .decl .one "x" (.const 1),
   .name "S" []]

theorem crepGetEidsFromDecls_panSimpDecls_fixture :
    crepGetEidsFromDecls id (panSimpDecls getEidsDecls) =
      crepGetEidsFromDecls id getEidsDecls :=
  crepGetEidsFromDecls_panSimpDecls id getEidsDecls

def getEidsPanSimpGuard : Bool :=
  crepGetEidsFromDecls id (panSimpDecls getEidsDecls) ==
    crepGetEidsFromDecls id getEidsDecls

#eval getEidsPanSimpGuard
#guard getEidsPanSimpGuard

end Flapjack.Test.PanGetEidsParity
