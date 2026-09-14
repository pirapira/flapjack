import Flapjack.PanValues
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_primitive`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:264-275`.
The expression results are supplied as optional values, matching the source
`OPT_MMAP (eval s)`.  The primitive handler, destination-shape check, and
local update are explicit parameters so this boundary preserves the original
ordering and source-state error behavior without reimplementing `eval_def`.
-/

namespace Flapjack

inductive PanHProgPrimitiveResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  deriving Repr

def panHProgPrimitive
    (sourceState : σ) (primitive : PanPrimitiveHandler α)
    (valid : σ → VarName → PanValue α → Bool)
    (setVar : σ → VarName → PanValue α → σ)
    (name : VarName) (operator : PrimOp)
    (operands : List (Option (PanValue α))) :
    PanFfiTree (PanHProgPrimitiveResult σ) :=
  match operands.mapM id with
  | some values =>
      match primitive operator values with
      | some value =>
          if valid sourceState name value then
            .ret (.normal (setVar sourceState name value))
          else
            .ret (.error sourceState)
      | none => .ret (.error sourceState)
  | none => .ret (.error sourceState)

end Flapjack
