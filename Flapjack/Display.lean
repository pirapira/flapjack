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

/-! A small executable depth measure supplies fuel for the display traversal.
    It is separate from Lean's erased `sizeOf` termination measure so the
    public helper remains compilable. -/
def panExpDepth : Exp α → Nat
  | .const _ => 1
  | .var _ _ => 1
  | .baseAddr => 1
  | .topAddr => 1
  | .bytesInWord => 1
  | .load _ address => 1 + panExpDepth address
  | .load32 address => 1 + panExpDepth address
  | .loadByte address => 1 + panExpDepth address
  | .rStruct fields => 1 + panExpDepthList fields
  | .nStruct _ fields => 1 + panExpDepthFieldList fields
  | .cmp _ left right => 1 + max (panExpDepth left) (panExpDepth right)
  | .op _ arguments => 1 + panExpDepthList arguments
  | .panOp _ arguments => 1 + panExpDepthList arguments
  | .rField _ value => 1 + panExpDepth value
  | .nField _ value => 1 + panExpDepth value
  | .shift _ left right => 1 + max (panExpDepth left) (panExpDepth right)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  panExpDepthList : List (Exp α) → Nat
    | [] => 0
    | expression :: expressions => max (panExpDepth expression) (panExpDepthList expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  panExpDepthFieldList : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, expression) :: fields => max (panExpDepth expression) (panExpDepthFieldList fields)
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-! A fuelled definition keeps recursion through source expression lists
    structural while the public wrapper is total for every finite AST. -/
def panExpToDisplayFuel [CakeDisplayWord α] : Nat → Exp α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .const value => itemWithWord "Const" value
  | _fuel + 1, .var kind name =>
      .item none "Var" [.string (varKindToString kind), .string name]
  | _fuel + 1, .baseAddr => .item none "BaseAddr" []
  | _fuel + 1, .topAddr => .item none "TopAddr" []
  | _fuel + 1, .bytesInWord => .item none "BytesInWord" []
  | fuel + 1, .load shape address =>
      .item none "MemLoad"
        [.string (Shape.shapeToString shape),
         panExpToDisplayFuel fuel address]
  | fuel + 1, .load32 address =>
      .item none "MemLoad32" [panExpToDisplayFuel fuel address]
  | fuel + 1, .loadByte address =>
      .item none "MemLoadByte" [panExpToDisplayFuel fuel address]
  | fuel + 1, .rStruct fields =>
      .item none "RawStruct" (fields.map (panExpToDisplayFuel fuel))
  | fuel + 1, .nStruct name fields =>
      .item none "NamedStruct"
        (.string name :: fields.map (fun (field, value) =>
          .tuple [.string field, .string ":=", panExpToDisplayFuel fuel value]))
  | fuel + 1, .cmp operator left right =>
      insertDisplayExpressions (cmpToDisplay operator)
        [panExpToDisplayFuel fuel left, panExpToDisplayFuel fuel right]
  | fuel + 1, .op operator arguments =>
      insertDisplayExpressions (binOpToDisplay operator)
        (arguments.map (panExpToDisplayFuel fuel))
  | fuel + 1, .panOp .mul arguments =>
      .item none "Mul" (arguments.map (panExpToDisplayFuel fuel))
  | fuel + 1, .rField index value =>
      .item none "RawField"
        [.string (toString index), panExpToDisplayFuel fuel value]
  | fuel + 1, .nField field value =>
      .item none "NamedField" [.string field, panExpToDisplayFuel fuel value]
  | fuel + 1, .shift operator left right =>
      insertDisplayExpressions (shiftToDisplay operator)
        [panExpToDisplayFuel fuel left, panExpToDisplayFuel fuel right]
termination_by fuel => fuel

def panExpToDisplay [CakeDisplayWord α] (expression : Exp α) : DisplayExpr :=
  panExpToDisplayFuel (panExpDepth expression + 1) expression

def primOpToDisplay : PrimOp → DisplayExpr
  | .addCarry => emptyDisplayItem "AddCarry"

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
