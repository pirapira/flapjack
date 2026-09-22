import Flapjack.Pancake.PanGlobals

/-!
# Original-domain parity for `pan_to_word$exp_ids_compile_globals`

The source theorem is
`cakeml/pancake/proofs/pan_to_wordProofScript.sml:135`:
`!ctxt p. exp_ids (compile ctxt p) = exp_ids p`.

The Flapjack counterpart is `Flapjack.globalCompileProg_expIds`.
-/

namespace Flapjack.Test.PanGlobalsExpIdsParity

open Flapjack

def expIdsContext : GlobalPassContext Nat :=
  { globals := [("g", (Shape.one, 4))], globalsSize := 4, maxGlobalsSize := 8,
    bytesInWord := 8, fromNat := fun n => n }

def expIdsProgram : Prog Nat :=
  .seq (.raise "E" (.const 1)) (.assign .global "g" (.const 2))

theorem globalCompileProg_expIds_fixture :
    expIds (globalCompileProg expIdsContext expIdsProgram) =
      expIds expIdsProgram :=
  globalCompileProg_expIds expIdsContext expIdsProgram

def expIdsCompileGuard : Bool :=
  expIds (globalCompileProg expIdsContext expIdsProgram) == ["E"] &&
    expIds expIdsProgram == ["E"]

#eval expIdsCompileGuard
#guard expIdsCompileGuard

/-! Cake's `compile_decs_no_exp_ids_main`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:174`). -/

def initializerDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 2), .exnDecl "E" .one]

theorem globalCompileInitializers_expIds_fixture :
    ∀ initializer ∈ globalCompileInitializers expIdsContext initializerDecls,
      expIds initializer = [] :=
  globalCompileInitializers_expIds expIdsContext initializerDecls

def initializerExpIdsGuard : Bool :=
  (globalCompileInitializers expIdsContext initializerDecls).all
    (fun initializer => expIds initializer == [])

#eval initializerExpIdsGuard
#guard initializerExpIdsGuard

/-! Cake's `compile_decs_exp_ids`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:153`). -/

def expIdsFunctionDecl : FunDecl Nat :=
  { name := "f", inline := false, exported := false, params := [],
    body := (.seq (.raise "E" (.const 1)) .tick), returnShape := .one }

def expIdsDecls : List (Decl Nat) :=
  [.function expIdsFunctionDecl, .decl .one "g" (.const 2)]

theorem globalCompileDecs_functions_expIds_fixture :
    (functions (globalCompileDecs expIdsContext expIdsDecls).functions).map
        (fun entry => expIds entry.2.2.1) =
      (functions expIdsDecls).map (fun entry => expIds entry.2.2.1) :=
  globalCompileDecs_functions_expIds expIdsContext expIdsDecls

def compileDecsExpIdsGuard : Bool :=
  (functions expIdsDecls).map (fun entry => expIds entry.2.2.1) == [["E"]]

#eval compileDecsExpIdsGuard
#guard compileDecsExpIdsGuard

end Flapjack.Test.PanGlobalsExpIdsParity
