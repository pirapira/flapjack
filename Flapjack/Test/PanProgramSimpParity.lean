import Flapjack.PanProgramSimp

namespace Flapjack.Test.PanProgramSimpParity

/-! Direct parity for Cake's `decs_stcnames_compile_prog`
    (`pan_simpProofScript.sml:1334-1341`): `pan_simp` must not change the
    struct-name context collected by `decs_stcnames` /
    `collectPanValueStructs`. -/

def fixture : List (Decl Nat) :=
  [.name "S" [("f1", .one), ("f2", .one)],
   .decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

theorem collectPanValueStructs_panSimpDecls_fixture :
    collectPanValueStructs (panSimpDecls fixture) [] =
      collectPanValueStructs fixture [] :=
  collectPanValueStructs_panSimpDecls fixture []

def namesGuard : Bool :=
  match collectPanValueStructs fixture [] with
  | some context => context.map Prod.fst == ["S"]
  | none => false

def parityGuard : Bool :=
  match collectPanValueStructs (panSimpDecls fixture) [],
      collectPanValueStructs fixture [] with
  | some simplified, some original => simplified.map Prod.fst == original.map Prod.fst
  | none, none => true
  | _, _ => false

#eval namesGuard
#guard namesGuard
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanProgramSimpParity
