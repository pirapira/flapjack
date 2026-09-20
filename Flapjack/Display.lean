import Flapjack.Language

/-!
The small display-language boundary used by Pancake's pass printer.

This is the Lean counterpart of `displayLang$sExp` and the basic helpers in
`presLangScript.sml`.  Keeping the trace parameter explicit preserves the
shape of Cake's `Item (trace option) name children`, even though the first
ported Pancake helpers below all use `NONE`.
-/

namespace Flapjack

inductive DisplayTrace where
  | cons (trace : Option DisplayTrace) (number : Nat)
  | union (left right : DisplayTrace)
  | sourceLoc (startLine startColumn endLine endColumn : Int)
  deriving Repr

inductive DisplayExpr where
  | item (trace : Option DisplayTrace) (name : String) (children : List DisplayExpr)
  | string (value : String)
  | tuple (children : List DisplayExpr)
  | list (children : List DisplayExpr)
  deriving Repr

def emptyDisplayItem (name : String) : DisplayExpr :=
  .string name

def opSizeToDisplay : OpSize → DisplayExpr
  | .op8 => emptyDisplayItem "byte"
  | .op16 => emptyDisplayItem "word16"
  | .opW => emptyDisplayItem "word"
  | .op32 => emptyDisplayItem "word32"

def insertDisplayExpressions (value : DisplayExpr)
    (children : List DisplayExpr) : DisplayExpr :=
  match value with
  | .string name => .item none name children
  | expression => expression

def varKindToDisplayString : VarKind → String
  | .global => "global"
  | .local => "local"

def primOpToDisplay : PrimOp → DisplayExpr
  | .addCarry => emptyDisplayItem "AddCarry"

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
