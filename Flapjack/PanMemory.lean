import Flapjack.PanValues

/-!
Flat source memory semantics.

CakeML's Pancake evaluator does not store a record as one memory cell.  It
flattens `RStruct` and `NStruct` values into consecutive words and reconstructs
them from a shape when loading.  This module ports that part of `panSem`: the
memory domain is explicit, failed reads and writes return `none`, and offsets
are measured in `bytesInWord` units.
-/

namespace Flapjack

abbrev PanFlatMemory (α : Type u) := α → Option α
abbrev PanMemoryDomain (α : Type u) := α → Bool

def panOffset [Add α] (bytesInWord address : α) : Nat → α
  | 0 => address
  | count + 1 => panOffset bytesInWord address count + bytesInWord

def panShapeFuel : Shape → Nat
  | .one => 1
  | .comb shapes => 1 + panShapeListFuel shapes
  | .named _ => 1
where
  panShapeListFuel : List Shape → Nat
    | [] => 0
    | shape :: shapes => panShapeFuel shape + panShapeListFuel shapes

def panShapeFieldsFuel : List (FieldName × Shape) → Nat
  | [] => 0
  | (_, shape) :: fields => 1 + panShapeFuel shape + panShapeFieldsFuel fields

def panStructContextFuel : StructContext → Nat
  | [] => 0
  | (_, info) :: context => panShapeFieldsFuel info.fields + panStructContextFuel context

def panValueFuel : PanValue α → Nat
  | .word _ => 1
  | .rStruct fields => 1 + panValueListFuel fields
  | .nStruct _ fields => 1 + panValueFieldListFuel fields
where
  panValueListFuel : List (PanValue α) → Nat
    | [] => 0
    | value :: values => panValueFuel value + panValueListFuel values

  panValueFieldListFuel : List (FieldName × PanValue α) → Nat
    | [] => 0
    | (_, value) :: fields => panValueFuel value + panValueFieldListFuel fields

def panValueWordsFuel : Nat → PanValue α → List α
  | 0, _ => []
  | fuel + 1, .word value => [value]
  | fuel + 1, .rStruct fields => panValueWordsListFuel fuel fields
  | fuel + 1, .nStruct _ fields => panValueWordsFieldListFuel fuel fields
where
  panValueWordsListFuel : Nat → List (PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, value :: values =>
        panValueWordsFuel fuel value ++ panValueWordsListFuel fuel values

  panValueWordsFieldListFuel : Nat → List (FieldName × PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, (_, value) :: fields =>
        panValueWordsFuel fuel value ++ panValueWordsFieldListFuel fuel fields

def panValueWords (value : PanValue α) : List α :=
  panValueWordsFuel (panValueFuel value + 1) value

def panFlatReadWord [BEq α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (address : α) : Option (PanValue α) :=
  if domain address then (memory address).map .word else none

def panFlatLoadFuel [BEq α] [OfNat α 0] [Add α]
    (context : StructContext) (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord : α) : Nat → Shape → α →
      Option (PanValue α)
  | 0, _, _ => none
  | fuel + 1, .one, address => panFlatReadWord domain memory address
  | fuel + 1, .comb shapes, address =>
      (panFlatLoadListFuel context domain memory bytesInWord fuel shapes address).map
        PanValue.rStruct
  | fuel + 1, .named name, address => do
      let info ← lookupInfo name context
      let fields ← panFlatLoadFieldsFuel context domain memory bytesInWord fuel
        info.fields address
      pure (.nStruct name fields)
termination_by fuel shape address => fuel
where
  panFlatLoadListFuel [BEq α] [OfNat α 0] [Add α]
      (context : StructContext) (domain : PanMemoryDomain α)
      (memory : PanFlatMemory α) (bytesInWord : α) : Nat → List Shape → α →
        Option (List (PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, shape :: shapes, address => do
        let value ← panFlatLoadFuel context domain memory bytesInWord fuel shape address
        let values ← panFlatLoadListFuel context domain memory bytesInWord fuel shapes
          (panOffset bytesInWord address (shapeSizeWithContext context shape))
        pure (value :: values)
    termination_by fuel shapes address => fuel

  panFlatLoadFieldsFuel [BEq α] [OfNat α 0] [Add α]
      (context : StructContext) (domain : PanMemoryDomain α)
      (memory : PanFlatMemory α) (bytesInWord : α) : Nat →
        List (FieldName × Shape) → α →
        Option (List (FieldName × PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, (field, shape) :: fields, address => do
        let value ← panFlatLoadFuel context domain memory bytesInWord fuel shape address
        let values ← panFlatLoadFieldsFuel context domain memory bytesInWord fuel fields
          (panOffset bytesInWord address (shapeSizeWithContext context shape))
        pure ((field, value) :: values)
    termination_by fuel fields address => fuel

def panFlatLoad [BEq α] [OfNat α 0] [Add α]
    (context : StructContext) (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α) (shape : Shape) :
    Option (PanValue α) :=
  if isWfShape context shape then
    panFlatLoadFuel context domain memory bytesInWord
      (panStructContextFuel context + panShapeFuel shape + 1) shape address
  else none

def panFlatStoreWord [BEq α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (address value : α) : Option (PanFlatMemory α) :=
  if domain address then
    some (updatePanValueMap memory address value)
  else none

def panFlatStoreWords [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord : α) : α → List α →
      Option (PanFlatMemory α)
  | address, [] => some memory
  | address, value :: values => do
      let memory ← panFlatStoreWord domain memory address value
      panFlatStoreWords domain memory bytesInWord
        (panOffset bytesInWord address 1) values

def panFlatStore [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α)
    (value : PanValue α) : Option (PanFlatMemory α) :=
  panFlatStoreWords domain memory bytesInWord address (panValueWords value)

def evalPanFlatExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α) : Exp α → Option (PanValue α)
  | .const value => some (.word value)
  | .var .local name => locals name
  | .var .global name => globals name
  | .rStruct fields =>
      (evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord fields).map .rStruct
  | .rField index expression => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields => do
      let info ← lookupInfo name structs
      let values ← evalPanFlatFields structs locals globals domain memory
        baseAddress topAddress bytesInWord fields
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let .word address := address | none
      panFlatLoad structs domain memory bytesInWord address shape
  | .load32 _ | .loadByte _ => none
  | .op operator arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right => some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left
      let right ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right
      match left, right with
      | .word left, .word right =>
          (evalPanShift operator left right).map .word
      | _, _ => none
  | .baseAddr => some (.word baseAddress)
  | .topAddr => some (.word topAddress)
  | .bytesInWord => some (.word bytesInWord)
termination_by expression => sizeOf expression
where
  evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      List (Exp α) → Option (List (PanValue α))
    | [] => some []
    | expression :: expressions => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord expressions
        pure (value :: values)
    termination_by expressions => sizeOf expressions

  evalPanFlatFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      List (FieldName × Exp α) → Option (List (FieldName × PanValue α))
    | [] => some []
    | (name, expression) :: fields => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression
        let values ← evalPanFlatFields structs locals globals domain memory
          baseAddress topAddress bytesInWord fields
        pure ((name, value) :: values)
    termination_by fields => sizeOf fields

def evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) : Option (List (PanValue α)) :=
  evalPanFlatExp.evalPanFlatExps structs locals globals domain memory
    baseAddress topAddress bytesInWord expressions

def evalPanFlatProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (primitive : PanPrimitiveHandler α) :
    Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (PanFlatMemory α) × List (PanValue α))
  | .skip => some (locals, globals, memory, [])
  | .dec name shape value body => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals domain memory primitive body
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .primitive name operator arguments => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      let .word address := address | none
      let memory ← panFlatStore domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .seq first second => do
      let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals domain memory primitive first
      if result.2.2.2.isEmpty then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 domain result.2.2.1 primitive second
      else pure result
  | .ite condition thenBranch elseBranch => do
      let condition ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord condition
      let .word condition := condition | none
      if condition != 0 then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive thenBranch
      else
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive elseBranch
  | .return value => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value
      pure (locals, globals, memory, [value])
  | .tick | .annot _ _ => some (locals, globals, memory, [])
  | _ => none
termination_by program => sizeOf program

def evalPanFlatProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) : Prog α →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × PanFlatMemory α × List (PanValue α)) :=
  evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals domain memory (fun _ _ => none)

end Flapjack
