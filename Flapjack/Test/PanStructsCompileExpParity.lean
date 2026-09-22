import Flapjack.Pancake.PanStructs

namespace Flapjack.Test.PanStructsCompileExpParity

/-! Direct parity for `pan_structs$compile_exp_def`
    (`pan_structsScript.sml:107`). The cases mirror the direct HOL fixture. -/
def context : StructPassContext :=
  { structs := [ ("Pair", { fields := [("left", .one),
      ("right", .comb [.one, .one])], size := 3 }) ]
    locals := [("local", .comb [.one, .one])]
    globals := [("global", .named "Pair")] }

def parityGuard : Bool :=
  (match structCompileExp context
      (.rStruct [.const 1, .const 2] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.rField 1 (.rStruct [.const 1, .const 2]) : Exp Nat) with
  | .rField 1 (.rStruct [.const 1, .const 2]) => true
  | _ => false) &&
  (match structCompileExp context
      (.nStruct "Pair" [("right", .const 2), ("left", .const 1)] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.nField "right" (.nStruct "Pair" []) : Exp Nat) with
  | .rField 1 (.rStruct []) => true
  | _ => false) &&
  (match structCompileExp context
      (.load (.named "Pair") (.const 0) : Exp Nat) with
  | .load (.comb [.one, .comb [.one, .one]]) (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.load32 (.const 0) : Exp Nat) with
  | .load32 (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.loadByte (.const 0) : Exp Nat) with
  | .loadByte (.const 0) => true
  | _ => false) &&
  (match structCompileExp context (.const 0 : Exp Nat) with
  | .const 0 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/- Direct parity for `pan_structs$compile_def` (`pan_structsScript.sml:157`).
   The declaration-local context is observable here: the body field lookup
   must use the source shape bound by `Dec`, while the emitted declaration
   carries the recursively compiled shape. -/
def compileProgParityGuard : Bool :=
  match structCompileProg context
      (.dec "value" (.named "Pair")
        (.nStruct "Pair" [("left", .const 1), ("right", .const 2)])
        (.return (.nField "right" (.var .local "value"))) : Prog Nat) with
  | .dec "value" (.comb [.one, .comb [.one, .one]])
      (.rStruct [.const 1, .const 2])
      (.return (.rField 1 (.var .local "value"))) => true
  | _ => false

#eval compileProgParityGuard
#guard compileProgParityGuard

/- Direct parity for `pan_structs$compile_decs_def`
   (`pan_structsScript.sml:213`).  This checks the reverse-recursive pass's
   final global context as well as each declaration's compiled shape. -/
def compileDeclsParityGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.decl (.named "Pair") "global"
      (.nStruct "Pair" [("left", .const 1), ("right", .const 2)]),
     .function
       { name := "read", inline := false, exported := false,
         params := [("pair", .named "Pair")],
         body := .return (.nField "right" (.var .local "pair")),
         returnShape := .named "Pair" },
     .exnDecl "E" (.named "Pair")]
  let initial : StructPassContext :=
    { structs := context.structs, locals := [], globals := [] }
  let (compiled, finalContext) := structCompileDecls declarations initial
  match finalContext.globals with
  | [("global", .named "Pair")] =>
      match compiled with
      | [.decl (.comb [.one, .comb [.one, .one]]) "global"
          (.rStruct [.const 1, .const 2]),
         .function declaration,
         .exnDecl "E" (.comb [.one, .comb [.one, .one]])] =>
          (match declaration.params with
          | [("pair", .comb [.one, .comb [.one, .one]])] => true
          | _ => false) &&
          (match declaration.returnShape with
          | .comb [.one, .comb [.one, .one]] => true
          | _ => false) &&
          match declaration.body with
          | .return (.rField 1 (.var .local "pair")) => true
          | _ => false
      | _ => false
  | _ => false

#eval compileDeclsParityGuard
#guard compileDeclsParityGuard

/- Cake `compile_exps_eq_map` (`pan_structsProofScript.sml:11`): the list
   compiler is the pointwise map of the expression compiler. -/
theorem structCompileExps_eq_map_fixture :
    structCompileExp.structCompileExps context
        ([.const 1, .const 2] : List (Exp Nat)) =
      [.const 1, .const 2] := by
  rw [structCompileExps_eq_map]
  simp [structCompileExp_const]

/- Cake `old_exp_shapes_eq` (`pan_structsProofScript.sml:679`): the list of
   old expression shapes is the pointwise map of the single-expression
   shape function. -/
theorem structOldExpShapes_eq_map_fixture :
    structOldExpShape.structOldExpShapes context
        ([.const 1, .var .local "local"] : List (Exp Nat)) =
      [.one, .comb [.one, .one]] := by
  rw [structOldExpShapes_eq_map]
  simp [structOldExpShape, context, lookupInfo]

end Flapjack.Test.PanStructsCompileExpParity
