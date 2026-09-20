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
  := varKindToString

/-! Cake's `word_to_display_def` prints words as an unpadded, upper-case
    hexadecimal number with a `0x` prefix.  Pancake source words are target
    words, so keep the natural-number projection explicit instead of using a
    potentially different `ToString` instance. -/
class CakeDisplayWord (α : Type u) where
  toNat : α → Nat

instance : CakeDisplayWord Nat where
  toNat := id

instance (width : Nat) : CakeDisplayWord (BitVec width) where
  toNat := BitVec.toNat

def cakeHexUpper : Char → Char
  | 'a' => 'A'
  | 'b' => 'B'
  | 'c' => 'C'
  | 'd' => 'D'
  | 'e' => 'E'
  | 'f' => 'F'
  | digit => digit

def natToCakeHex (value : Nat) : String :=
  "0x" ++ String.ofList ((Nat.toDigits 16 value).map cakeHexUpper)

def wordToDisplay [CakeDisplayWord α] (value : α) : DisplayExpr :=
  emptyDisplayItem (natToCakeHex (CakeDisplayWord.toNat value))

def itemWithWord [CakeDisplayWord α] (name : String) (value : α) : DisplayExpr :=
  .item none name [wordToDisplay value]

def binOpToDisplay : BinOp → DisplayExpr
  | .add => emptyDisplayItem "Add"
  | .sub => emptyDisplayItem "Sub"
  | .and => emptyDisplayItem "And"
  | .or => emptyDisplayItem "Or"
  | .xor => emptyDisplayItem "Xor"

def cmpToDisplay : Cmp → DisplayExpr
  | .equal => emptyDisplayItem "Equal"
  | .lower => emptyDisplayItem "Lower"
  | .less => emptyDisplayItem "Less"
  | .test => emptyDisplayItem "Test"
  | .notEqual => emptyDisplayItem "NotEqual"
  | .notLower => emptyDisplayItem "NotLower"
  | .notLess => emptyDisplayItem "NotLess"
  | .notTest => emptyDisplayItem "NotTest"

def shiftToDisplay : Shift → DisplayExpr
  | .lsl => emptyDisplayItem "Lsl"
  | .lsr => emptyDisplayItem "Lsr"
  | .asr => emptyDisplayItem "Asr"
  | .ror => emptyDisplayItem "Ror"

def panExpToDisplay [CakeDisplayWord α] : Exp α → DisplayExpr
  | .const value => itemWithWord "Const" value
  | .var kind name =>
      .item none "Var" [.string (varKindToString kind), .string name]
  | .baseAddr => .item none "BaseAddr" []
  | .topAddr => .item none "TopAddr" []
  | .bytesInWord => .item none "BytesInWord" []
  | .load shape address =>
      .item none "MemLoad"
        [.string (Shape.shapeToString shape),
         panExpToDisplay address]
  | .load32 address => .item none "MemLoad32" [panExpToDisplay address]
  | .loadByte address => .item none "MemLoadByte" [panExpToDisplay address]
  | .rStruct fields => .item none "RawStruct" (panExpToDisplayList fields)
  | .nStruct name fields =>
      .item none "NamedStruct"
        (.string name :: panExpToDisplayFieldList fields)
  | .cmp operator left right =>
      insertDisplayExpressions (cmpToDisplay operator)
        [panExpToDisplay left, panExpToDisplay right]
  | .op operator arguments =>
      insertDisplayExpressions (binOpToDisplay operator)
        (panExpToDisplayList arguments)
  | .panOp .mul arguments => .item none "Mul" (panExpToDisplayList arguments)
  | .rField index value =>
      .item none "RawField"
        [.string (toString index), panExpToDisplay value]
  | .nField field value =>
      .item none "NamedField" [.string field, panExpToDisplay value]
  | .shift operator left right =>
      insertDisplayExpressions (shiftToDisplay operator)
        [panExpToDisplay left, panExpToDisplay right]
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  panExpToDisplayList : List (Exp α) → List DisplayExpr
    | [] => []
    | expression :: expressions =>
        panExpToDisplay expression :: panExpToDisplayList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  panExpToDisplayFieldList : List (FieldName × Exp α) → List DisplayExpr
    | [] => []
    | (field, expression) :: fields =>
        .tuple [.string field, .string ":=", panExpToDisplay expression] ::
          panExpToDisplayFieldList fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def primOpToDisplay : PrimOp → DisplayExpr
  | .addCarry => emptyDisplayItem "AddCarry"

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
