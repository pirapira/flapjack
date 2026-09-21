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


/-! Regression for Cake's `state_rel_imp_evaluate_decls`
    (`pan_simpProofScript.sml:1303-1331`): the declaration-level evaluator
    preserves the state relation whose only non-trivial component simplifies
    every function body with `pan_simp`. -/

def relationState : PanValueProgramState Nat :=
  { structs := [], globals := fun _ => none,
    functions := [("f", [], (.seq (.skip : Prog Nat) (.skip : Prog Nat)))],
    returnShapes := [], parameterShapes := [], exceptions := [],
    memory := fun _ => none, baseAddress := 0, topAddress := 0, bytesInWord := 8 }

def relationDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := (.seq (.skip : Prog Nat) (.skip : Prog Nat)), returnShape := .one }]

theorem relationState_self :
    panValueProgramStateRel relationState
      { relationState with
        functions := panValueFunctionsSimp relationState.functions } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem relationDecls_preserved (s' : PanValueProgramState Nat)
    (hs : evalPanValueDeclarations relationState relationDecls = some s') :
    ∃ t', evalPanValueDeclarations
        { relationState with functions := panValueFunctionsSimp relationState.functions }
        (panSimpDecls relationDecls) = some t' ∧ panValueProgramStateRel s' t' :=
  panValueProgramStateRel_evalPanValueDeclarations relationState _ relationState_self
    relationDecls none s' hs

end Flapjack.Test.PanProgramSimpParity

