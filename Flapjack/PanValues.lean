import Flapjack.Semantics

/-!
Structured source values and the corresponding executable expression/state
semantics.  The original scalar evaluator in `Semantics.lean` is useful for
the first compiler slices, but the Pancake source language distinguishes words
from records and named records.  This file preserves that distinction and
matches the value/shape checks in CakeML's `panSem` evaluator.
-/

namespace Flapjack

inductive PanValue (α : Type u) where
  | word (value : α)
  | rStruct (fields : List (PanValue α))
  | nStruct (name : StructName) (fields : List (FieldName × PanValue α))
  deriving Repr

def panValueShape (context : StructContext) : PanValue α → Shape
  | .word _ => .one
  | .rStruct fields => .comb (fields.map (panValueShape context))
  | .nStruct name _ => .named name
termination_by value => sizeOf value

def panShapeMatches : Shape → Shape → Bool
  | .one, .one => true
  | .named left, .named right => left == right
  | .comb left, .comb right => panShapeListMatches left right
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
where
  panShapeListMatches : List Shape → List Shape → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        panShapeMatches left right && panShapeListMatches leftRest rightRest
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right
    decreasing_by
      all_goals first | decreasing_trivial

def panValueFieldsHaveShapes (context : StructContext) :
    List (FieldName × Shape) → List (FieldName × PanValue α) → Bool
  | [], [] => true
  | (expectedName, expectedShape) :: expected,
      (actualName, actualValue) :: actual =>
      expectedName == actualName &&
        panShapeMatches (panValueShape context actualValue) expectedShape &&
        panValueFieldsHaveShapes context expected actual
  | _, _ => false

def lookupPanValueField (name : FieldName) :
    List (FieldName × PanValue α) → Option (PanValue α)
  | [] => none
  | (candidate, value) :: fields =>
      if candidate == name then some value else lookupPanValueField name fields

def evalPanValueExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) : Exp α → Option (PanValue α)
  | .const value => some (.word value)
  | .var .local name => locals name
  | .var .global name => globals name
  | .rStruct fields =>
      (evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord fields).map .rStruct
  | .rField index expression => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let values ← evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      if panShapeMatches (panValueShape structs value) shape then some value else none
  | .load32 address | .loadByte address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match value with
      | .word value => some (.word value)
      | _ => none
  | .op operator arguments => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] =>
          some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right => some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          (evalPanShift operator left right).map .word
      | _, _ => none
  | .baseAddr => some (.word baseAddress)
  | .topAddr => some (.word topAddress)
  | .bytesInWord => some (.word bytesInWord)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (Exp α) → Option (List (PanValue α))
    | [] => some []
    | expression :: expressions => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  evalPanValueFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α))
    | [] => some []
    | (name, expression) :: fields => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanValueFields structs locals globals memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values)
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def updatePanValueMap [BEq γ] (values : γ → Option α)
    (name : γ) (value : α) : γ → Option α :=
  fun current => if current == name then some value else values current

def updatePanValueMemory [BEq α] (memory : α → Option (PanValue α))
    (address : α) (value : PanValue α) : α → Option (PanValue α) :=
  updatePanValueMap memory address value

def restorePanValueLocal [BEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) : VarName → Option (PanValue α) :=
  fun current => if current == name then oldValue else locals current

def evalPanValueProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) :
    Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α))
  | .skip => some (locals, globals, memory, [])
  | .dec name shape value body => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanValueProg structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals memory body
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .store address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      pure (locals, globals, updatePanValueMemory memory address value, [])
  | .store32 address value | .storeByte address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      pure (locals, globals, updatePanValueMemory memory address (.word value), [])
  | .return value => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      pure (locals, globals, memory, [value])
  | .seq first second => do
      let result ← evalPanValueProg structs baseAddress topAddress bytesInWord
        locals globals memory first
      if result.2.2.2.isEmpty then
        evalPanValueProg structs baseAddress topAddress bytesInWord
          result.1 result.2.1 result.2.2.1 second
      else pure result
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord condition
      let .word condition := condition | none
      if condition != 0 then
        evalPanValueProg structs baseAddress topAddress bytesInWord
          locals globals memory thenBranch
      else
        evalPanValueProg structs baseAddress topAddress bytesInWord
          locals globals memory elseBranch
  | .shMemLoad _ kind name address => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      let value ← memory address
      match kind with
      | .local => pure (updatePanValueMap locals name value, globals, memory, [])
      | .global => pure (locals, updatePanValueMap globals name value, memory, [])
  | .shMemStore _ address value => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let .word value := value | none
      pure (locals, globals, updatePanValueMemory memory address (.word value), [])
  | .tick | .annot _ _ => some (locals, globals, memory, [])
  | _ => none
termination_by program => sizeOf program

theorem evalPanValueExp_rField_word
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (left right : α) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      (.rField 1 (.rStruct [.const left, .const right])) = some (.word right) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]

end Flapjack
