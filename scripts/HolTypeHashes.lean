import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.Pancake.Proofs.PanToCrep.CompileProgParams
import Flapjack.Pancake.Proofs.PanToCrep.Primop
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.WordLang
import Flapjack.RiscV.CorrectnessEncoding

open Lean Elab Command Flapjack

/-! Export kernel-visible declaration types, not source-text approximations.
Binder names and metadata do not affect the proposition and are removed before
serializing the elaborated expression. The pinned Lean toolchain determines the
format of the structural `repr` consumed by `check_hol_type_hashes.py`. -/
private partial def canonicalType : Expr → Expr
  | .forallE _ type body info =>
      .forallE `_ (canonicalType type) (canonicalType body) info
  | .lam _ type body info =>
      .lam `_ (canonicalType type) (canonicalType body) info
  | .letE _ type value body nondep =>
      .letE `_ (canonicalType type) (canonicalType value) (canonicalType body) nondep
  | .app fn arg => .app (canonicalType fn) (canonicalType arg)
  | .proj name index body => .proj name index (canonicalType body)
  | .mdata _ body => canonicalType body
  | expr => expr

elab "#emit_hol_type_hashes" : command => do
  let env ← getEnv
  for (name, ref) in HolRef.all env do
    match env.find? name with
    | none => throwError "missing declaration {name}"
    | some info =>
        let payload := Json.mkObj [
          ("lean_name", toJson name.toString),
          ("hol_path", toJson ref.path),
          ("hol_name", toJson ref.name),
          ("type_expr", toJson (reprStr (canonicalType info.type)))]
        liftIO <| IO.println payload.compress

#emit_hol_type_hashes
