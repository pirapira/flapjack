import Flapjack.Language
import Flapjack.Loop

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

def primOpToDisplay : PrimOp → DisplayExpr
  | .addCarry => emptyDisplayItem "AddCarry"

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

def cakeEscapeChar : Char → String
  | '\t' => "\\t"
  | '\n' => "\\n"
  | '\\' => "\\\\"
  | '"' => "\\\""
  | character => String.ofList [character]

def cakeEscapeString (value : String) : String :=
  "\"" ++ String.ofList (value.toList.flatMap (fun character =>
    (cakeEscapeChar character).toList)) ++ "\""

def separateDisplayLines (name : String) (children : List DisplayExpr) : DisplayExpr :=
  .list (.string name :: children)

/-! Program display uses a fuel derived from the nesting of program bodies.
    The fuel is an implementation detail; every recursive call consumes one,
    so the public helper has the same total behavior as Cake's definition. -/
def panProgDepth : Prog α → Nat
  | .skip => 1
  | .dec _ _ _ body => 1 + panProgDepth body
  | .assign _ _ _ => 1
  | .primitive _ _ _ => 1
  | .store _ _ => 1
  | .store32 _ _ => 1
  | .storeByte _ _ => 1
  | .seq first second => 1 + max (panProgDepth first) (panProgDepth second)
  | .ite _ thenBranch elseBranch =>
      1 + max (panProgDepth thenBranch) (panProgDepth elseBranch)
  | .while _ body => 1 + panProgDepth body
  | .break => 1
  | .continue => 1
  | .call (some (_, some (_, _, handler))) _ _ => 1 + panProgDepth handler
  | .call _ _ _ => 1
  | .decCall _ _ _ _ body => 1 + panProgDepth body
  | .extCall _ _ _ _ _ => 1
  | .raise _ _ => 1
  | .return _ => 1
  | .shMemLoad _ _ _ _ => 1
  | .shMemStore _ _ _ => 1
  | .tick => 1
  | .annot _ _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def panProgToDisplayFuel [CakeDisplayWord α] : Nat → Prog α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .skip => emptyDisplayItem "skip"
  | _fuel + 1, .shMemLoad size kind name address =>
      .item none "shared_mem_load"
        [opSizeToDisplay size, .string (varKindToString kind), .string name,
         panExpToDisplay address]
  | _fuel + 1, .shMemStore size address value =>
      .item none "shared_mem_store"
        [opSizeToDisplay size, panExpToDisplay address, panExpToDisplay value]
  | _fuel + 1, .extCall function configuration configurationLength array arrayLength =>
      .item none "ext_call"
        [.string function, panExpToDisplay configuration,
         panExpToDisplay configurationLength, panExpToDisplay array,
         panExpToDisplay arrayLength]
  | fuel + 1, .ite condition thenBranch elseBranch =>
      .item none "if"
        [panExpToDisplay condition, panProgToDisplayFuel fuel thenBranch,
         panProgToDisplayFuel fuel elseBranch]
  | fuel + 1, .while condition body =>
      .item none "while" [panExpToDisplay condition, panProgToDisplayFuel fuel body]
  | fuel + 1, .dec name shape value body =>
      .item none "dec"
        [.tuple [.string "local", .string (Shape.shapeToString shape),
          .string name, .string ":=", panExpToDisplay value],
         panProgToDisplayFuel fuel body]
  | _fuel + 1, .assign kind name value =>
      .tuple [.string (varKindToString kind), .string name, .string ":=",
        panExpToDisplay value]
  | _fuel + 1, .primitive name operator arguments =>
      .tuple [.string name, .string ":=",
        insertDisplayExpressions (primOpToDisplay operator)
          (panExpToDisplayList arguments)]
  | _fuel + 1, .store address value =>
      .tuple [.string "mem", panExpToDisplay address, .string ":=",
        panExpToDisplay value]
  | _fuel + 1, .store32 address value =>
      .tuple [.string "mem", panExpToDisplay address, .string ":=",
        .string "32bit", panExpToDisplay value]
  | _fuel + 1, .storeByte address value =>
      .tuple [.string "mem", panExpToDisplay address, .string ":=",
        .string "byte", panExpToDisplay value]
  | _fuel + 1, .annot tag text =>
      .item none "annot" [.string (cakeEscapeString tag), .string (cakeEscapeString text)]
  | _fuel + 1, .tick => emptyDisplayItem "tick"
  | _fuel + 1, .break => emptyDisplayItem "break"
  | _fuel + 1, .continue => emptyDisplayItem "continue"
  | _fuel + 1, .return value => .item none "return" [panExpToDisplay value]
  | _fuel + 1, .raise exception value =>
      .item none "raise" [.string exception, panExpToDisplay value]
  | fuel + 1, .seq first second =>
      separateDisplayLines "seq"
        ((panSeqs first ++ panSeqs second).map (panProgToDisplayFuel fuel))
  | _fuel + 1, .call none function arguments =>
      .item none "tail_call"
        [.string function, .tuple (panExpToDisplayList arguments)]
  | fuel + 1, .call (some (none, handler)) function arguments =>
      .item none "call"
        [.string function, .tuple (panExpToDisplayList arguments),
         panProgToDisplayFuelHandler fuel handler]
  | fuel + 1, .call (some (some (_, destination), handler)) function arguments =>
      .tuple [.string destination, .string ":=",
        .item none "call"
          [.string function, .tuple (panExpToDisplayList arguments),
           panProgToDisplayFuelHandler fuel handler]]
  | fuel + 1, .decCall destination shape function arguments body =>
      .item none "dec"
        [.tuple [.string (Shape.shapeToString shape), .string destination,
          .string ":=", .item none "call"
            [.string function, .tuple (panExpToDisplayList arguments)]],
         panProgToDisplayFuel fuel body]
termination_by fuel => fuel
where
  panExpToDisplayList : List (Exp α) → List DisplayExpr
    | [] => []
    | expression :: expressions =>
        panExpToDisplay expression :: panExpToDisplayList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  panProgToDisplayFuelHandler : Nat → Option (ExceptionId × VarName × Prog α) → DisplayExpr
    | _, none => emptyDisplayItem "no_handler"
    | 0, some _ => emptyDisplayItem "display-depth-exhausted"
    | fuel + 1, some (exception, handlerVariable, program) =>
        .item none "handler"
          [.tuple [.string exception, .string handlerVariable,
            panProgToDisplayFuel fuel program]]
  termination_by fuel => fuel
  decreasing_by all_goals decreasing_trivial

def panProgToDisplay [CakeDisplayWord α] (program : Prog α) : DisplayExpr :=
  panProgToDisplayFuel (panProgDepth program + 1) program

/-! Exact source counterpart of Cake's `loop_exp_to_display_def`
    (`pan_passesScript.sml:508-530`).  The extra Loop constructors retained by
    the executable carrier are given stable names, while every constructor in
    the source equation is reproduced verbatim. -/
def loopExpToDisplayFuel [CakeDisplayWord α] : Nat → LoopExp α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .const value => itemWithWord "Const" value
  | _fuel + 1, .var name => .item none "Var" [.string (toString name)]
  | _fuel + 1, .baseAddr => .item none "BaseAddr" []
  | _fuel + 1, .topAddr => .item none "TopAddr" []
  | _fuel + 1, .lookup address => itemWithWord "Lookup" address
  | fuel + 1, .load address =>
      .item none "MemLoad" [loopExpToDisplayFuel fuel address]
  | fuel + 1, .op operator arguments =>
      .item none "Op"
        (binOpToDisplay operator :: arguments.map (loopExpToDisplayFuel fuel))
  | fuel + 1, .shift operator left right =>
      .item none "Shift"
        [shiftToDisplay operator,
         loopExpToDisplayFuel fuel left,
         loopExpToDisplayFuel fuel right]
  | fuel + 1, .crepOp .mul arguments =>
      .item none "Mul" (arguments.map (loopExpToDisplayFuel fuel))
  | fuel + 1, .cmp operator left right =>
      insertDisplayExpressions (cmpToDisplay operator)
        [loopExpToDisplayFuel fuel left, loopExpToDisplayFuel fuel right]

def loopExpDepth : LoopExp α → Nat
  | .const _ | .var _ | .lookup _ | .baseAddr | .topAddr => 1
  | .load address => 1 + loopExpDepth address
  | .op _ arguments | .crepOp _ arguments => 1 + loopExpDepthList arguments
  | .cmp _ left right | .shift _ left right =>
      1 + max (loopExpDepth left) (loopExpDepth right)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  loopExpDepthList : List (LoopExp α) → Nat
    | [] => 0
    | expression :: expressions =>
        max (loopExpDepth expression) (loopExpDepthList expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def loopExpToDisplay [CakeDisplayWord α] (expression : LoopExp α) : DisplayExpr :=
  loopExpToDisplayFuel (loopExpDepth expression + 1) expression

/-! Exact source counterpart of Cake's `pan_fun_to_display_def`
    (`pan_passesScript.sml:311-330`). -/
def panFunToDisplay [CakeDisplayWord α] : Decl α → DisplayExpr
  | .function declaration =>
      .tuple [.string "func", .string (Shape.shapeToString declaration.returnShape),
        .string declaration.name,
        .tuple (declaration.params.map (fun (name, shape) =>
          .tuple [.string name, .string ":", .string (Shape.shapeToString shape)])),
        panProgToDisplay declaration.body]
  | .decl shape name expression =>
      .tuple [.string "global", .string (Shape.shapeToString shape), .string name,
        .string ":=", panExpToDisplay expression]
  | .name name fields =>
      .tuple [.string "struct", .string name,
        .tuple (fields.map (fun (field, shape) =>
          .tuple [.string field, .string ":", .string (Shape.shapeToString shape)]))]
  | .exnDecl exception shape =>
      .tuple [.string "exception", .string exception, .string ":",
        .string (Shape.shapeToString shape)]

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
