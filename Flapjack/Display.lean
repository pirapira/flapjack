import Flapjack.Pancake.PanLang
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.LoopLang
import Flapjack.NumSet

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

/-! The small string-tree and pretty intermediate languages used by Cake's
    `display_to_str_tree`/`str_tree_to_strs` boundary. -/
inductive DisplayStrTree where
  | str (value : String)
  | trees (children : List DisplayStrTree)
  | grabLine (tree : DisplayStrTree)

inductive DisplayPretty where
  | parenthesis (body : DisplayPretty)
  | string (value : String)
  | append (left : DisplayPretty) (lineBreak : Bool) (right : DisplayPretty)
  | size (width : Nat) (body : DisplayPretty)

def displayToStrTree : DisplayExpr → DisplayStrTree
  | .item _ name children =>
      .trees (.str name :: children.map displayToStrTree)
  | .string value => .str value
  | .tuple [] => .str "()"
  | .tuple children => .trees (children.map displayToStrTree)
  | .list [] => .str "()"
  | .list children => .trees ((children.map displayToStrTree).map .grabLine)

def displayNewlines : List DisplayPretty → DisplayPretty
  | [] => .string ""
  | [pretty] => pretty
  | pretty :: pretties => .append pretty true (displayNewlines pretties)

def displayV2Pretty : DisplayStrTree → DisplayPretty
  | .str value => .string value
  | .grabLine tree => .size 100000 (displayV2Pretty tree)
  | .trees children => .parenthesis (displayNewlines (children.map displayV2Pretty))

def displayGetSize : DisplayPretty → Nat
  | .size width _ => width
  | .append left _ right => displayGetSize left + displayGetSize right + 1
  | .parenthesis body => displayGetSize body + 2
  | .string _ => 0

def displayGetNextSize : DisplayPretty → Nat
  | .size width _ => width
  | .append left _ _ => displayGetNextSize left
  | .parenthesis body => displayGetNextSize body + 2
  | .string _ => 0

def displayAnnotate : DisplayPretty → DisplayPretty
  | .string value => .size value.length (.string value)
  | .parenthesis body =>
      let annotated := displayAnnotate body
      .size (displayGetSize annotated + 2) (.parenthesis annotated)
  | .append left lineBreak right =>
      .append (displayAnnotate left) lineBreak (displayAnnotate right)
  | .size width body => .size width (displayAnnotate body)

def displayRemoveAll : DisplayPretty → DisplayPretty
  | .parenthesis body => .parenthesis (displayRemoveAll body)
  | .string value => .string value
  | .append left _ right =>
      .append (displayRemoveAll left) false (displayRemoveAll right)
  | .size _ body => displayRemoveAll body

def displaySmartRemove : Nat → Nat → DisplayPretty → DisplayPretty
  | _, _, .string value => .string value
  | indent, column, .size width body =>
      if column + width < 70 then
        displayRemoveAll body
      else
        displaySmartRemove indent column body
  | indent, column, .parenthesis body =>
      .parenthesis (displaySmartRemove (indent + 1) (column + 1) body)
  | indent, column, .append left _lineBreak right =>
      let leftSize := displayGetSize left
      let rightSize := displayGetNextSize right
      if column + leftSize + rightSize < 50 then
        .append (displaySmartRemove indent column left) false
          (displaySmartRemove indent (column + leftSize) right)
      else
        .append (displaySmartRemove indent column left) true
          (displaySmartRemove indent indent right)
termination_by _ _ pretty => sizeOf pretty

def displayPrettyDepth : DisplayPretty → Nat
  | .string _ => 1
  | .size _ body | .parenthesis body => 1 + displayPrettyDepth body
  | .append left _ right =>
      1 + max (displayPrettyDepth left) (displayPrettyDepth right)

def displayFlattenFuel : Nat → String → DisplayPretty → List String → List String
  | 0, _, _, rest => rest
  | fuel + 1, indent, .size _ body, rest => displayFlattenFuel fuel indent body rest
  | fuel + 1, indent, .parenthesis body, rest =>
      "(" :: displayFlattenFuel fuel (indent ++ "   ") body (")" :: rest)
  | _fuel + 1, _indent, .string value, rest => value :: rest
  | fuel + 1, indent, .append left lineBreak right, rest =>
      let rightStrings := displayFlattenFuel fuel indent right rest
      displayFlattenFuel fuel indent left
        ((if lineBreak then indent else " ") :: rightStrings)

def displayFlatten (indent : String) (pretty : DisplayPretty)
    (rest : List String) : List String :=
  displayFlattenFuel (displayPrettyDepth pretty + 1) indent pretty rest

def displayStrTreeToStrings (ending : String) (tree : DisplayStrTree) : List String :=
  displayFlatten "\n"
    (displaySmartRemove 0 0
      (displayAnnotate (displayV2Pretty tree))) [ending]

def mapAppendDisplayStrings (render : α → List String) : List α → List String
  | [] => []
  | value :: values => render value ++ mapAppendDisplayStrings render values

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

def itemWithNat (name : String) (value : Nat) : DisplayExpr :=
  .item none name [.string (toString value)]

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

/-! Exact source counterpart of Cake's `crep_exp_to_display_def`
    (`pan_passesScript.sml:348-372`).  Crepe variables are numeric, so the
    source `num_to_display` helper is represented by `toString` here. -/
def crepExpToDisplayFuel [CakeDisplayWord α] : Nat → CrepExp α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .const value => itemWithWord "Const" value
  | _fuel + 1, .loadGlob value => itemWithWord "LoadGlob" value
  | _fuel + 1, .var name => .item none "Var" [.string (toString name)]
  | _fuel + 1, .baseAddr => .item none "BaseAddr" []
  | _fuel + 1, .topAddr => .item none "TopAddr" []
  | fuel + 1, .load address =>
      .item none "MemLoad" [crepExpToDisplayFuel fuel address]
  | fuel + 1, .load32 address =>
      .item none "MemLoad32" [crepExpToDisplayFuel fuel address]
  | fuel + 1, .loadByte address =>
      .item none "MemLoadByte" [crepExpToDisplayFuel fuel address]
  | fuel + 1, .cmp operator left right =>
      insertDisplayExpressions (cmpToDisplay operator)
        [crepExpToDisplayFuel fuel left, crepExpToDisplayFuel fuel right]
  | fuel + 1, .op operator arguments =>
      insertDisplayExpressions (binOpToDisplay operator)
        (arguments.map (crepExpToDisplayFuel fuel))
  | fuel + 1, .crepOp .mul arguments =>
      .item none "Mul" (arguments.map (crepExpToDisplayFuel fuel))
  | fuel + 1, .shift operator left right =>
      insertDisplayExpressions (shiftToDisplay operator)
        [crepExpToDisplayFuel fuel left, crepExpToDisplayFuel fuel right]

def crepExpDepth : CrepExp α → Nat
  | .const _ | .loadGlob _ | .var _ | .baseAddr | .topAddr => 1
  | .load address | .load32 address | .loadByte address => 1 + crepExpDepth address
  | .op _ arguments | .crepOp _ arguments => 1 + crepExpDepthList arguments
  | .cmp _ left right | .shift _ left right =>
      1 + max (crepExpDepth left) (crepExpDepth right)
termination_by expression => sizeOf expression
where
  crepExpDepthList : List (CrepExp α) → Nat
    | [] => 0
    | expression :: expressions =>
        max (crepExpDepth expression) (crepExpDepthList expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def crepExpToDisplay [CakeDisplayWord α] (expression : CrepExp α) : DisplayExpr :=
  crepExpToDisplayFuel (crepExpDepth expression + 1) expression

/-! Exact source counterpart of Cake's `crep_prog_to_display_def`
    (`pan_passesScript.sml:394-489`). -/
def crepProgToDisplayFuel [CakeDisplayWord α] : Nat → CrepProg α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .skip => emptyDisplayItem "skip"
  | _fuel + 1, .shMem operator name address =>
      let memoryPrefix := match operator with
        | .load => [.string "load", .string "word"]
        | .load8 => [.string "load", .string "byte"]
        | .load16 => [.string "load", .string "word16"]
        | .load32 => [.string "load", .string "word32"]
        | .store => [.string "store", .string "word"]
        | .store8 => [.string "store", .string "byte"]
        | .store16 => [.string "store", .string "word16"]
        | .store32 => [.string "store", .string "word32"]
      .item none "shared_mem"
        (memoryPrefix ++ [.string (toString name), crepExpToDisplay address])
  | _fuel + 1, .extCall function configuration configurationLength array arrayLength =>
      .item none "ext_call"
        [.string function, .string (toString configuration),
         .string (toString configurationLength), .string (toString array),
         .string (toString arrayLength)]
  | _fuel + 1, .storeGlob address value =>
      .item none "store_glob"
        [wordToDisplay address, crepExpToDisplay value]
  | fuel + 1, .ite condition thenBranch elseBranch =>
      .item none "if"
        [crepExpToDisplay condition,
         crepProgToDisplayFuel fuel thenBranch,
         crepProgToDisplayFuel fuel elseBranch]
  | fuel + 1, .while condition body =>
      .item none "while"
        [crepExpToDisplay condition, crepProgToDisplayFuel fuel body]
  | fuel + 1, .dec name value body =>
      .item none "dec"
        [.tuple [.string (toString name), .string ":=", crepExpToDisplay value],
         crepProgToDisplayFuel fuel body]
  | _fuel + 1, .assign name value =>
      .tuple [.string (toString name), .string ":=", crepExpToDisplay value]
  | _fuel + 1, .primitive names operator arguments =>
      .tuple [.tuple (names.map (fun name => .string (toString name))),
        .string ":=",
        insertDisplayExpressions (primOpToDisplay operator)
          (arguments.map (fun name => .string (toString name)))]
  | _fuel + 1, .store address value =>
      .tuple [.string "mem", crepExpToDisplay address, .string ":=",
        crepExpToDisplay value]
  | _fuel + 1, .store32 address value =>
      .tuple [.string "mem", crepExpToDisplay address, .string ":=",
        .string "32bit", crepExpToDisplay value]
  | _fuel + 1, .storeByte address value =>
      .tuple [.string "mem", crepExpToDisplay address, .string ":=",
        .string "byte", crepExpToDisplay value]
  | _fuel + 1, .tick => emptyDisplayItem "tick"
  | _fuel + 1, .break label => itemWithNat "break" label
  | _fuel + 1, .continue label => itemWithNat "continue" label
  | _fuel + 1, .return values =>
      .item none "return" (values.map crepExpToDisplay)
  | _fuel + 1, .raise exception => itemWithWord "raise" exception
  | fuel + 1, .seq first second =>
      .list (.string "seq" ::
        ((crepSeqs first ++ crepSeqs second).map
          (crepProgToDisplayFuel fuel)))
  | fuel + 1, .call none function arguments =>
      .item none "tail_call"
        [.string function, .tuple (arguments.map crepExpToDisplay)]
  | fuel + 1, .call (some ([], handler)) function arguments =>
      .item none "call"
        [.string function, .tuple (arguments.map crepExpToDisplay),
         crepProgToDisplayHandler fuel handler]
  | fuel + 1, .call (some (names, handler)) function arguments =>
      .tuple [.tuple (names.map (fun name => .string (toString name))),
        .string ":=",
        .item none "call"
          [.string function, .tuple (arguments.map crepExpToDisplay),
           crepProgToDisplayHandler fuel handler]]
termination_by fuel => fuel
where
  crepProgToDisplayHandler [CakeDisplayWord α] :
      Nat → Option (α × CrepProg α) → DisplayExpr
    | _, none => emptyDisplayItem "no_handler"
    | 0, some _ => emptyDisplayItem "display-depth-exhausted"
    | fuel + 1, some (exception, program) =>
        .item none "handler"
          [.tuple [wordToDisplay exception,
            crepProgToDisplayFuel fuel program]]
    termination_by fuel => fuel
    decreasing_by all_goals decreasing_trivial

def crepProgDepth : CrepProg α → Nat
  | .skip | .assign _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ |
      .storeByte _ _ | .storeGlob _ _ | .shMem _ _ _ | .extCall _ _ _ _ _ |
      .break _ | .continue _ | .tick | .raise _ | .return _ => 1
  | .dec _ _ body | .while _ body => 1 + crepProgDepth body
  | .ite _ thenBranch elseBranch =>
      1 + max (crepProgDepth thenBranch) (crepProgDepth elseBranch)
  | .seq first second => 1 + max (crepProgDepth first) (crepProgDepth second)
  | .call (some (_, some (_, handler))) _ _ => 1 + crepProgDepth handler
  | .call _ _ _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def crepProgToDisplay [CakeDisplayWord α] (program : CrepProg α) : DisplayExpr :=
  crepProgToDisplayFuel (crepProgDepth program + 1) program

/-! Exact source counterpart of Cake's `crep_fun_to_display_def`
    (`pan_passesScript.sml:492-499`). -/
def crepFunToDisplay [CakeDisplayWord α] (name : FunName) (parameters : List Nat)
    (body : CrepProg α) : DisplayExpr :=
  .tuple [.string "func", .string name,
    .tuple (parameters.map (fun parameter => .string (toString parameter))),
    crepProgToDisplay body]

/-! Exact source counterpart of Cake's `crep_to_strs_def`
    (`pan_passesScript.sml:500-505`). -/
def crepToStrs [CakeDisplayWord α]
    (functions : List (FunName × List Nat × CrepProg α)) : List String :=
  mapAppendDisplayStrings
    (fun function =>
      let (name, parameters, body) := function
      displayStrTreeToStrings "\n\n"
        (displayToStrTree (crepFunToDisplay name parameters body))) functions

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

/-! Exact source counterpart of Cake's `pan_to_strs_def`
    (`pan_passesScript.sml:340-346`). -/
def panToStrs [CakeDisplayWord α] (declarations : List (Decl α)) : List String :=
  mapAppendDisplayStrings
    (fun declaration =>
      displayStrTreeToStrings "\n\n"
        (displayToStrTree (panFunToDisplay declaration))) declarations

def numToDisplay (number : Nat) : DisplayExpr :=
  .string (toString number)

def numsToDisplay (name : String) (numbers : List Nat) : DisplayExpr :=
  .item none name (numbers.map numToDisplay)

def displayNumSetString : List Nat → String
  | [] => ""
  | [number] => toString number
  | number :: numbers => toString number ++ "," ++ displayNumSetString numbers

/-! `num_set_to_display` traverses Cake's sorted sptree list, not the input
    insertion order.  Rebuild that observable order through the shared
    list-backed `NumSet` port. -/
def numSetToDisplay (names : List Nat) : DisplayExpr :=
  .string ("{" ++ displayNumSetString (NumSet.fromList names) ++ "}")

def displayList (children : List DisplayExpr) : DisplayExpr :=
  .list children

def loopLookupDisplayName : Nat → List (Nat × String) → Option String
  | _, [] => none
  | number, (candidate, name) :: names =>
      if number == candidate then some name else loopLookupDisplayName number names

def loopAttachName (names : List (Nat × String)) (number : Option Nat) : String :=
  match number with
  | none => "none"
  | some number =>
      match loopLookupDisplayName number names with
      | none => toString number
      | some name => name ++ "@" ++ toString number

def loopRegImmToDisplay [CakeDisplayWord α] (value : RegImm α) : DisplayExpr :=
  match value with
  | .reg number => .item none "Reg" [numToDisplay number]
  | .imm value => itemWithWord "Imm" value

def loopMemOpToDisplay : CrepMemOp → DisplayExpr
  | .load => emptyDisplayItem "Load"
  | .load8 => emptyDisplayItem "Load8"
  | .load16 => emptyDisplayItem "Load16"
  | .load32 => emptyDisplayItem "Load32"
  | .store => emptyDisplayItem "Store"
  | .store8 => emptyDisplayItem "Store8"
  | .store16 => emptyDisplayItem "Store16"
  | .store32 => emptyDisplayItem "Store32"

def loopArithToDisplay : LoopArith → DisplayExpr
  | .longMul leftHigh rightHigh leftLow rightLow =>
      numsToDisplay "long_mul" [leftHigh, rightHigh, leftLow, rightLow]
  | .longDiv leftHigh rightHigh leftLow rightLow quotient =>
      numsToDisplay "long_div" [leftHigh, rightHigh, leftLow, rightLow, quotient]
  | .div destination dividend divisor =>
      numsToDisplay "div" [destination, dividend, divisor]


def loopProgHandlerToDisplay [CakeDisplayWord α]
    (render : LoopProg α → DisplayExpr) :
    Option (Nat × LoopProg α × LoopProg α × List Nat) → DisplayExpr
  | none => emptyDisplayItem "no_handler"
  | some (exception, handlerBody, returnBody, live) =>
      .item none "handler"
        [.tuple [numToDisplay exception,
                 render handlerBody,
                 render returnBody,
                 numSetToDisplay live]]

def loopProgDepth : LoopProg α → Nat
  | .skip | .arith _ | .assign _ _ | .primitive _ _ _ | .setGlobal _ _ => 1
  | .seq first second => 1 + max (loopProgDepth first) (loopProgDepth second)
  | .ffi _ _ _ _ _ _ | .raise _ | .return _ | .tick
  | .break _ | .continue _ | .fail | .load32 _ _ | .loadByte _ _
  | .store32 _ _ | .storeByte _ _ | .locValue _ _ | .shMem _ _ _ => 1
  | .ite _ _ _ thenBranch elseBranch _ =>
      1 + max (loopProgDepth thenBranch) (loopProgDepth elseBranch)
  | .loop _ body _ | .mark body => 1 + loopProgDepth body
  | .store _ _ => 1
  | .call _ _ _ handler => 1 + loopProgHandlerDepth handler
termination_by program => sizeOf program
where
  loopProgHandlerDepth :
      Option (Nat × LoopProg α × LoopProg α × List Nat) → Nat
    | none => 0
    | some (_, handlerBody, returnBody, _) =>
        max (loopProgDepth handlerBody) (loopProgDepth returnBody)
    termination_by handler => sizeOf handler

/-! Exact source counterpart of Cake's `loop_prog_to_display_def` and its
    handler equation (`pan_passesScript.sml:549-631`).  The fuel wrapper is
    executable for the recursive Loop carrier while preserving each source
    display constructor and list/tuple boundary. -/
def loopProgToDisplayFuel [CakeDisplayWord α]
    (names : List (Nat × String)) : Nat → LoopProg α → DisplayExpr
  | 0, _ => emptyDisplayItem "display-depth-exhausted"
  | _fuel + 1, .skip => emptyDisplayItem "skip"
  | _fuel + 1, .arith operation => loopArithToDisplay operation
  | _fuel + 1, .assign number expression =>
      .tuple [numToDisplay number, .string ":=", loopExpToDisplay expression]
  | _fuel + 1, .primitive destinations operator arguments =>
      .tuple [
        .tuple (destinations.map numToDisplay),
        .string ":=",
        insertDisplayExpressions (primOpToDisplay operator)
          (arguments.map numToDisplay)]
  | _fuel + 1, .setGlobal address expression =>
      .item none "set_global" [wordToDisplay address, loopExpToDisplay expression]
  | fuel + 1, .seq first second =>
      separateDisplayLines "seq"
        ((loopSeqs first ++ loopSeqs second).map
          (loopProgToDisplayFuel names fuel))
  | _fuel + 1, .ffi function configuration configurationLength array arrayLength live =>
      .item none "ffi"
        ([.string function,
          numToDisplay configuration,
          numToDisplay configurationLength,
          numToDisplay array,
          numToDisplay arrayLength] ++ [numSetToDisplay live])
  | _fuel + 1, .raise exception => numsToDisplay "raise" [exception]
  | _fuel + 1, .return values => numsToDisplay "return" values
  | _fuel + 1, .tick => emptyDisplayItem "tick"
  | _fuel + 1, .break label => numsToDisplay "break" [label]
  | _fuel + 1, .continue label => numsToDisplay "continue" [label]
  | _fuel + 1, .fail => emptyDisplayItem "fail"
  | _fuel + 1, .load32 address destination =>
      numsToDisplay "load_32" [address, destination]
  | _fuel + 1, .loadByte address destination =>
      numsToDisplay "load_byte" [address, destination]
  | _fuel + 1, .store32 address value => numsToDisplay "store_32" [address, value]
  | _fuel + 1, .storeByte address value => numsToDisplay "store_byte" [address, value]
  | _fuel + 1, .locValue destination source =>
      .item none "loc_value"
        [.string (loopAttachName names (some destination)), numToDisplay source]
  | _fuel + 1, .shMem operator name address =>
      .tuple [.string "share_mem", loopMemOpToDisplay operator,
        numToDisplay name, loopExpToDisplay address]
  | fuel + 1, .ite operator condition right thenBranch elseBranch live =>
      .item none "if"
        [.tuple [cmpToDisplay operator, numToDisplay condition,
                 loopRegImmToDisplay right],
         loopProgToDisplayFuel names fuel thenBranch,
         loopProgToDisplayFuel names fuel elseBranch,
         numSetToDisplay live]
  | fuel + 1, .loop liveIn body liveOut =>
      .item none "loop"
        [numSetToDisplay liveIn,
         loopProgToDisplayFuel names fuel body,
         numSetToDisplay liveOut]
  | fuel + 1, .mark body =>
      .item none "mark" [loopProgToDisplayFuel names fuel body]
  | _fuel + 1, .store address value =>
      .tuple [.string "mem", loopExpToDisplay address,
        .string ":=", numToDisplay value]
  | fuel + 1, .call returns target arguments handler =>
      let targetDisplay := .string (loopAttachName names target)
      let callDisplay := .item none "call"
        [targetDisplay,
         displayList (arguments.map numToDisplay),
         match returns with
         | none => numSetToDisplay []
         | some (_, live) => numSetToDisplay live,
         loopProgHandlerToDisplay
           (loopProgToDisplayFuel names fuel) handler]
      match returns with
      | none => .item none "tail_call"
          [targetDisplay, displayList (arguments.map numToDisplay)]
      | some (destinations, _) =>
          .tuple [displayList (destinations.map numToDisplay), .string ":=", callDisplay]

def loopProgToDisplay [CakeDisplayWord α]
    (names : List (Nat × String)) (program : LoopProg α) : DisplayExpr :=
  loopProgToDisplayFuel names (loopProgDepth program + 1) program

/-! Exact source counterpart of Cake's `loop_fun_to_display_def`
    (`pan_passesScript.sml:646-652`). -/
def loopFunToDisplay [CakeDisplayWord α]
    (names : List (Nat × String))
    (function : Nat × List Nat × LoopProg α) : DisplayExpr :=
  let (number, arguments, body) := function
  .tuple [
    .string "func",
    .string (loopAttachName names (some number)),
    .tuple (arguments.map numToDisplay),
    loopProgToDisplay names body]

/-! Exact source counterpart of Cake's `loop_to_strs_def`
    (`pan_passesScript.sml:654-658`). -/
def loopToStrs [CakeDisplayWord α]
    (names : List (Nat × String))
    (functions : List (Nat × List Nat × LoopProg α)) : List String :=
  mapAppendDisplayStrings
    (fun function =>
      displayStrTreeToStrings "\n\n"
        (displayToStrTree (loopFunToDisplay names function))) functions

/-! The typed output-boundary counterpart of Cake's `any_pan_prog_pp_def`
    (`pan_passesScript.sml:660-666`).  Backend Cake stages are represented by
    their already-rendered string stream because the source/backend ASTs are
    not part of Flapjack's source-shaped language. -/
inductive AnyPanProg (α : Type u) where
  | pan (program : List (Decl α))
  | crep (program : List (FunName × List Nat × CrepProg α))
  | loop (program : List (Nat × List Nat × LoopProg α))
      (names : List (Nat × String))
  | cake (rendered : List String)

def anyPanProgPp [CakeDisplayWord α] : AnyPanProg α → List String
  | .pan program => panToStrs program
  | .crep program => crepToStrs program
  | .loop program names => loopToStrs names program
  | .cake rendered => rendered

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
