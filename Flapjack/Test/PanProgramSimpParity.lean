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

/-! Focused regressions for the `OPT_MMAP` helper counterparts used by
    `compile_correct` (`pan_simpProofScript.sml:394`, `:500`, `:509`). -/

/-- The `some` branch of `opt_mmap_eq_some_helper`. -/
theorem list_mapM_eq_some_of_eq_some_fixture :
    ([3, 5] : List Nat).mapM (fun n => if n == 4 then none else some (n + 1)) =
      some [4, 6] :=
  list_mapM_eq_some_of_eq_some (fun n : Nat => if n == 4 then none else some (n + 1))
    (fun n : Nat => if n == 4 then none else some (n + 1)) [3, 5] [4, 6] (by decide)
    (fun _ _ _ h => h)

/-- `OPT_MMAP_NONE`: the failing element is `4`. -/
theorem list_mapM_eq_none_exists_fixture :
    ∃ x ∈ ([3, 4, 5] : List Nat),
      (fun n => if n == 4 then none else some (n + 1)) x = none :=
  list_mapM_eq_none_exists (fun n : Nat => if n == 4 then none else some (n + 1)) [3, 4, 5]
    (by decide)

/-- `OPT_MMAP_NONE'`: member `4` makes the whole map fail. -/
theorem list_mapM_eq_none_of_mem_fixture :
    ([3, 4, 5] : List Nat).mapM (fun n => if n == 4 then none else some (n + 1)) =
      none :=
  list_mapM_eq_none_of_mem (f := fun n : Nat => if n == 4 then none else some (n + 1))
    (x := 4) (xs := [3, 4, 5]) (by decide) (by decide)

end Flapjack.Test.PanProgramSimpParity
