import Flapjack.Pancake.PanGlobals

/-!
# Pancake declaration predicate/count parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_decl_predicates_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:234-253`.
-/

namespace Flapjack.Test.PanLangDeclPredicatesParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:234-253 (is_decl/is_exn_decl/is_name/size_of_eids)"

def declaration : Decl Nat := .decl .one "g" (.const 7)

def exceptionDeclaration : Decl Nat := .exnDecl "E" .one

def nameDeclaration : Decl Nat := .name "S" []

def panSimpDeclarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.const 0), returnShape := .one },
   .exnDecl "F" .one]

theorem size_of_eids_pan_simp_preserves :
    sizeOfEids (panSimpDecls panSimpDeclarations) =
      sizeOfEids panSimpDeclarations := by
  exact sizeOfEids_panSimpDecls panSimpDeclarations

def parityGuard : Bool :=
  isDecl declaration &&
  !isDecl exceptionDeclaration &&
  isExnDecl exceptionDeclaration &&
  !isExnDecl declaration &&
  isName nameDeclaration &&
  !isName declaration &&
  sizeOfEids ([] : List (Decl Nat)) == 0 &&
  sizeOfEids [declaration, nameDeclaration, exceptionDeclaration] == 1 &&
  sizeOfEids (panSimpDecls panSimpDeclarations) ==
    sizeOfEids panSimpDeclarations

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:234-253 (is_decl/is_exn_decl/is_name/size_of_eids)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangDeclPredicatesParity
