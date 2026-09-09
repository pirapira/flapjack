import Flapjack.PanValues
import Flapjack.PanMemoryModel

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
  | _fuel + 1, .word value => [value]
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
  | _fuel + 1, .one, address => panFlatReadWord domain memory address
  | fuel + 1, .comb shapes, address =>
      (panFlatLoadListFuel context domain memory bytesInWord fuel shapes address).map
        PanValue.rStruct
  | fuel + 1, .named name, address => do
      let info ← lookupInfo name context
      let fields ← panFlatLoadFieldsFuel context domain memory bytesInWord fuel
        info.fields address
      pure (.nStruct name fields)
termination_by fuel _shape _address => fuel
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
    termination_by fuel _shapes _address => fuel

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
    termination_by fuel _fields _address => fuel

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
  | _address, [] => some memory
  | address, value :: values => do
      let memory ← panFlatStoreWord domain memory address value
      panFlatStoreWords domain memory bytesInWord
        (panOffset bytesInWord address 1) values

def panFlatStore [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α)
    (value : PanValue α) : Option (PanFlatMemory α) :=
  panFlatStoreWords domain memory bytesInWord address (panValueWords value)

def panFlatLoadWithAccess [BEq α] [OfNat α 0] [Add α]
    (context : StructContext) (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α) (shape : Shape)
    (memoryAccess : Option (PanMemoryAccess α) := none) :
    Option (PanValue α) :=
  match memoryAccess, shape with
  | some access, .one => (access.readWord domain memory address).map .word
  | _, _ => panFlatLoad context domain memory bytesInWord address shape

def panFlatStoreWithAccess [BEq α] [Add α] (domain : PanMemoryDomain α)
    (memory : PanFlatMemory α) (bytesInWord address : α)
    (value : PanValue α) (memoryAccess : Option (PanMemoryAccess α) := none) :
    Option (PanFlatMemory α) :=
  match memoryAccess, value with
  | some access, .word value => access.storeWord domain memory address value
  | _, _ => panFlatStore domain memory bytesInWord address value

def evalPanFlatExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α) :
    (expression : Exp α) → (memoryAccess : Option (PanMemoryAccess α) := none) →
      Option (PanValue α)
  | .const value, _ => some (.word value)
  | .var .local name, _ => locals name
  | .var .global name, _ => globals name
  | .rStruct fields, memoryAccess =>
      (evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)).map .rStruct
  | .rField index expression, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields, memoryAccess => do
      let info ← lookupInfo name structs
      let values ← evalPanFlatFields structs locals globals domain memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      panFlatLoadWithAccess structs domain memory bytesInWord address shape memoryAccess
  | .load32 address, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => panFlatReadWord domain memory address
      | some access => (access.read32 domain memory bytesInWord address).map .word
  | .loadByte address, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => panFlatReadWord domain memory address
      | some access => (access.readByte domain memory bytesInWord address).map .word
  | .op operator arguments, memoryAccess => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      let values ← values.mapM fun value => match value with
        | .word value => some value
        | _ => none
      match memoryAccess with
      | none =>
          match values with
          | [left, right] => some (.word (evalPanBinOp operator left right))
          | _ => none
      | some access => (access.wordOp operator values).map .word
  | .panOp .mul arguments, memoryAccess => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right, memoryAccess => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right =>
          match memoryAccess with
          | none => some (.word (evalPanCmp operator left right))
          | some access => some (.word (access.compare operator left right))
      | _, _ => none
  | .shift operator left right, memoryAccess => do
      let left ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right =>
          match memoryAccess with
          | none => (evalPanShift operator left right).map .word
          | some access => (access.shift operator left right).map .word
      | _, _ => none
  | .baseAddr, _ => some (.word baseAddress)
  | .topAddr, _ => some (.word topAddress)
  | .bytesInWord, _ => some (.word bytesInWord)
termination_by expression => sizeOf expression
where
  evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      (expressions : List (Exp α)) →
      (memoryAccess : Option (PanMemoryAccess α) := none) →
        Option (List (PanValue α))
    | [], _ => some []
    | expression :: expressions, memoryAccess => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord expressions (memoryAccess := memoryAccess)
        pure (value :: values)
    termination_by expressions => sizeOf expressions

  evalPanFlatFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
      (baseAddress topAddress bytesInWord : α) :
      (fields : List (FieldName × Exp α)) →
      (memoryAccess : Option (PanMemoryAccess α) := none) →
        Option (List (FieldName × PanValue α))
    | [], _ => some []
    | (name, expression) :: fields, memoryAccess => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanFlatFields structs locals globals domain memory
          baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
        pure ((name, value) :: values)
    termination_by fields => sizeOf fields

def evalPanFlatExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α)) (memoryAccess : Option (PanMemoryAccess α) := none) :
      Option (List (PanValue α)) :=
  evalPanFlatExp.evalPanFlatExps structs locals globals domain memory
    baseAddress topAddress bytesInWord expressions memoryAccess

def evalPanFlatProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (primitive : PanPrimitiveHandler α) :
    (program : Prog α) → (memoryAccess : Option (PanMemoryAccess α) := none) →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (PanFlatMemory α) × List (PanValue α))
  | .skip, _ => some (locals, globals, memory, [])
  | .dec name shape value body, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals domain memory primitive body
          (memoryAccess := memoryAccess)
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .local name value then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .assign .global name value, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .global name value then
        pure (locals, updatePanValueMap globals name value, memory, [])
      else none
  | .primitive name operator arguments, memoryAccess => do
      let values ← evalPanFlatExps structs locals globals domain memory
        baseAddress topAddress bytesInWord arguments memoryAccess
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let memory ← panFlatStoreWithAccess domain memory bytesInWord address value memoryAccess
      pure (locals, globals, memory, [])
  | .store32 address value, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => none
        | some access => access.store32 domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .storeByte address value, memoryAccess => do
      let address ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => none
        | some access => access.storeByte domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .seq first second, memoryAccess => do
      let result ← evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals domain memory primitive first (memoryAccess := memoryAccess)
      if result.2.2.2.isEmpty then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 domain result.2.2.1 primitive second
          (memoryAccess := memoryAccess)
      else pure result
  | .ite condition thenBranch elseBranch, memoryAccess => do
      let condition ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
      let .word condition := condition | none
      if condition != 0 then
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive thenBranch (memoryAccess := memoryAccess)
      else
        evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals domain memory primitive elseBranch (memoryAccess := memoryAccess)
  | .return value, memoryAccess => do
      let value ← evalPanFlatExp structs locals globals domain memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValuePayloadWithinLimit structs value then
        pure (locals, globals, memory, [value])
      else none
  | .tick, _ | .annot _ _, _ => some (locals, globals, memory, [])
  | _, _ => none
termination_by program => sizeOf program

def evalPanFlatProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α)
    (program : Prog α) (memoryAccess : Option (PanMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × PanFlatMemory α × List (PanValue α)) :=
  evalPanFlatProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals domain memory (fun _ _ => none) program memoryAccess

inductive PanFlatControlResult (α : Type u) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : PanFlatMemory α)

abbrev PanFlatFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
      Option (VarName → Option (PanValue α))

def restorePanFlatControlLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanFlatControlResult α → PanFlatControlResult α
  | .normal locals globals memory =>
      .normal (restorePanValueLocal locals name oldValue) globals memory
  | .returned locals globals memory values =>
      .returned (restorePanValueLocal locals name oldValue) globals memory values
  | .raised locals globals memory exception value =>
      .raised (restorePanValueLocal locals name oldValue) globals memory exception value
  | .broke locals globals memory =>
      .broke (restorePanValueLocal locals name oldValue) globals memory
  | .continued locals globals memory =>
      .continued (restorePanValueLocal locals name oldValue) globals memory

mutual
  def evalPanFlatCallWithPrimitiveAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
      (baseAddress topAddress bytesInWord : α)
      (domain : PanMemoryDomain α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → PanFlatMemory α →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanFlatControlResult α)
    | 0, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, contracts => do
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel calleeLocals globals memory body
          (contracts := contracts)
        match result with
        | .normal _ calleeGlobals calleeMemory =>
            pure (.normal locals calleeGlobals calleeMemory)
        | .returned _ calleeGlobals calleeMemory values =>
            if panValueReturnValid structs contracts function values &&
                panValueValuesWithinLimit structs values then
              match info with
              | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values)
              | some (destination, _) => do
                  let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                    destination values
                    (structs := structs)
                  pure (.normal locals globals calleeMemory)
            else none
        | .raised _ calleeGlobals calleeMemory exception value =>
            if panValueExceptionValid structs contracts exception value &&
                panValuePayloadWithinLimit structs value then
              match info with
              | some (_, some (caught, handlerVariable, handlerProgram)) =>
                  if caught == exception then
                    if panValueHandlerValid structs contracts locals handlerVariable value then
                      evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                        baseAddress topAddress bytesInWord domain fuel
                        (updatePanValueMap locals handlerVariable value)
                        calleeGlobals calleeMemory handlerProgram
                        (contracts := contracts)
                    else none
                  else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
              | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
            else none
        | .broke _ calleeGlobals calleeMemory =>
            pure (.broke (fun _ => none) calleeGlobals calleeMemory)
        | .continued _ calleeGlobals calleeMemory =>
            pure (.continued (fun _ => none) calleeGlobals calleeMemory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanFlatProgFuelWithPrimitiveAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
      (baseAddress topAddress bytesInWord : α)
      (domain : PanMemoryDomain α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → PanFlatMemory α → Prog α →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanFlatControlResult α)
    | 0, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _contracts =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .dec name shape value body, contracts => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel
            (updatePanValueMap locals name value) globals memory body
            (contracts := contracts)
          pure (restorePanFlatControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, _contracts => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .assign .global name value, _contracts => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments, _contracts => do
        let values ← evalPanFlatExps structs locals globals domain memory
          baseAddress topAddress bytesInWord arguments
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, _contracts => do
        let address ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord address
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        let .word address := address | none
        let memory ← panFlatStore domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .seq first second, contracts => do
        let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory first
          (contracts := contracts)
        match result with
        | .normal locals globals memory =>
            evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
              baseAddress topAddress bytesInWord domain fuel locals globals memory second
              (contracts := contracts)
        | result => pure result
    | fuel + 1, locals, globals, memory, .ite condition thenBranch elseBranch, contracts => do
        let condition ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word condition := condition | none
        if condition != 0 then
          evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory thenBranch
            (contracts := contracts)
        else
          evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory elseBranch
            (contracts := contracts)
    | fuel + 1, locals, globals, memory, .call info function arguments, contracts =>
        evalPanFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory info function arguments
          (contracts := contracts)
    | fuel + 1, locals, globals, memory, .decCall name shape function arguments body, contracts => do
        let oldValue := locals name
        let result ← evalPanFlatCallWithPrimitiveAndFfi structs functions ffi primitive
          baseAddress topAddress bytesInWord domain fuel locals globals memory
          none function arguments (contracts := contracts)
        match result with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                baseAddress topAddress bytesInWord domain fuel
                (updatePanValueMap locals name value) globals memory body
                (contracts := contracts)
              pure (restorePanFlatControlLocal name oldValue result)
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value)
        | _ => none
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, _contracts => do
        let configuration ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configuration
        let configurationLength ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord configurationLength
        let array ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord array
        let arrayLength ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord arrayLength
        let .word configuration := configuration | none
        let .word configurationLength := configurationLength | none
        let .word array := array | none
        let .word arrayLength := arrayLength | none
        let locals ← ffi function configuration configurationLength array arrayLength locals
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while condition body, contracts => do
        let evaluatedCondition ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord condition
        let .word conditionValue := evaluatedCondition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
            baseAddress topAddress bytesInWord domain fuel locals globals memory body
            (contracts := contracts)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
                baseAddress topAddress bytesInWord domain fuel locals globals memory
                (.while condition body) (contracts := contracts)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _contracts =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _contracts =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, contracts => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panValueExceptionValid structs contracts exception value &&
            panValuePayloadWithinLimit structs value then
          pure (.raised (fun _ => none) globals memory exception value)
        else none
    | _fuel + 1, locals, globals, memory, .return value, _contracts => do
        let value ← evalPanFlatExp structs locals globals domain memory
          baseAddress topAddress bytesInWord value
        if panValuePayloadWithinLimit structs value then
          pure (.returned (fun _ => none) globals memory [value])
        else none
    | _fuel + 1, locals, globals, memory, .tick, _contracts |
        _fuel + 1, locals, globals, memory, .annot _ _, _contracts =>
        pure (.normal locals globals memory)
    | _, _, _, _, _, _ => none
    termination_by fuel _ _ _ _ => fuel
end

def evalPanFlatProgWithPrimitiveAndFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (ffi : PanFlatFfiHandler α) (primitive : PanPrimitiveHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) (program : Prog α)
    (contracts : Option PanValueCallContracts := none) :
    Option (PanFlatControlResult α) :=
  evalPanFlatProgFuelWithPrimitiveAndFfi structs functions ffi primitive
    baseAddress topAddress bytesInWord domain fuel locals globals memory program
    (contracts := contracts)

def evalPanFlatProgWithCallsAndFfi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (ffi : PanFlatFfiHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (domain : PanMemoryDomain α) (memory : PanFlatMemory α) (program : Prog α)
    (contracts : Option PanValueCallContracts := none) :
    Option (PanFlatControlResult α) :=
  evalPanFlatProgWithPrimitiveAndFfi structs functions ffi (fun _ _ => none)
    baseAddress topAddress bytesInWord fuel locals globals domain memory program
    (contracts := contracts)

end Flapjack
