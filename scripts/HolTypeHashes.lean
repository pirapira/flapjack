import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.AstHOL
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.Compiler.Backend.LabSem
import Flapjack.Compiler.Backend.LabProps
import Flapjack.Compiler.Backend.StackNames
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.AppList
import Flapjack.Misc.Sptree
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.PanLang.Exp
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.PanToCrep.ExpHdlExact
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanToCrep.Primop
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.Semantics.CrepSem.StateExact
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.LoopProps
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Semantics.PanProps.MemByteArray
import Flapjack.Pancake.Semantics.PanProps.LocalisedExpSimps
import Flapjack.Pancake.Semantics.PanProps.NamelessExpSimps
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.LookupCode
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt
import Flapjack.Pancake.Semantics.PanSem.MemStore32Alt
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip
import Flapjack.Misc.GoodDimindex
import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Semantics.PanSem.StateExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact
import Flapjack.Pancake.Semantics.PanSem.DecExact
import Flapjack.Pancake.Semantics.PanSem.ReturnRaiseExact
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact
import Flapjack.Pancake.Semantics.PanSem.ClockExact
import Flapjack.Pancake.Semantics.PanSem.StateSimpExact
import Flapjack.Pancake.Semantics.PanSem.StateDefsExact
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.WordConvs
import Flapjack.RiscV.CorrectnessEncoding
import Flapjack.Compiler.Backend.StackProps
import Flapjack.Pancake.PanStructs

open Lean Elab Command Flapjack

/-! Export kernel-visible declaration types and definition bodies, not
source-text approximations. Binder names and metadata do not affect the
proposition and are removed before serializing the elaborated expression. The
pinned Lean toolchain determines the format of the structural `repr` consumed
by `check_hol_type_hashes.py`.

Theorem proof terms are deliberately excluded: they may be refactored without
changing the reviewed statement. Definition and `opaque` bodies are included
because a tagged definition body can drift without changing its elaborated
type. -/
private partial def canonicalExpr : Expr → Expr
  | .forallE _ type body info =>
      .forallE `_ (canonicalExpr type) (canonicalExpr body) info
  | .lam _ type body info =>
      .lam `_ (canonicalExpr type) (canonicalExpr body) info
  | .letE _ type value body nondep =>
      .letE `_ (canonicalExpr type) (canonicalExpr value) (canonicalExpr body) nondep
  | .app fn arg => .app (canonicalExpr fn) (canonicalExpr arg)
  | .proj name index body => .proj name index (canonicalExpr body)
  | .mdata _ body => canonicalExpr body
  | expr => expr

/-- The body of a tagged definition or `opaque` declaration, if present. -/
private def definitionBody? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

elab "#emit_hol_type_hashes" : command => do
  let env ← getEnv
  for (name, ref) in HolRef.all env do
    match env.find? name with
    | none => throwError "missing declaration {name}"
    | some info =>
        let mut fields : List (String × Json) := [
          ("lean_name", toJson name.toString),
          ("hol_path", toJson ref.path),
          ("hol_name", toJson ref.name),
          ("type_expr", toJson (reprStr (canonicalExpr info.type))),
          ("qualifiers", Json.mkObj [
            ("list_as_array", toJson ref.listAsArray),
            ("names_as_string", toJson ref.namesAsString),
            ("names_as_string_boundary", toJson ref.namesAsStringBoundary),
            ("fmap_as_finite_support", toJson ref.fmapAsFiniteSupport),
            ("fmap_as_finite_support_result", toJson ref.fmapAsFiniteSupportResult)])]
        match definitionBody? info with
        | some body =>
            fields := fields ++ [("value_expr", toJson (reprStr (canonicalExpr body)))]
        | none => pure ()
        liftIO <| IO.println (Json.mkObj fields).compress

#emit_hol_type_hashes
