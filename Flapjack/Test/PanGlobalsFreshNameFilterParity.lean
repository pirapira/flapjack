import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsFreshNameFilterParity

open Flapjack

/-! Regression for the tagged HOL lemmas `fresh_name_correct`
    (`pan_globalsProofScript.sml:993`), `fresh_name_correct'`
    (`pan_globalsProofScript.sml:1003`), and `FILTER_decs_fperm_decs`
    (`pan_globalsProofScript.sml:2832`). -/

def functionDeclaration : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }

def declarations : List (Decl Nat) :=
  [functionDeclaration,
   .decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T"),
   .decl .one "h" (.const 9)]

theorem freshNameCorrectFixture :
    globalFreshName "x" ["x", "x'", "y"] ∉ ["x", "x'", "y"] :=
  fresh_name_correct "x" ["x", "x'", "y"]

theorem freshNameCorrectSubsetFixture
    (hmem : globalFreshName "x" ["x", "y"] ∈ (["x"] : List String)) : False :=
  fresh_name_correct' "x" ["x", "y"] ["x"] hmem
    (by
      intro candidate hmember
      simp only [List.mem_cons, List.mem_nil_iff] at hmember ⊢
      exact Or.inl (by simpa using hmember))

theorem filterDecsFpermDecsFixture :
    globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        (globalRenameDecls "f" "b" declarations) =
      globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations :=
  FILTER_decs_fperm_decs "f" "b" declarations

def freshNameFilterGuard : Bool :=
  (!(["x", "x'", "y"].contains (globalFreshName "x" ["x", "x'", "y"]))) &&
    ((exceptionEntries (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration)
        (globalRenameDecls "f" "b" declarations))).length ==
      (exceptionEntries (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration)
        declarations)).length)

#guard freshNameFilterGuard

def runChecks : IO Bool := do
  let ok ←
    if freshNameFilterGuard then
      IO.println "PASS pan_globals fresh_name_correct and FILTER_decs_fperm_decs"
      pure true
    else
      pure false
  pure ok

end Flapjack.Test.PanGlobalsFreshNameFilterParity