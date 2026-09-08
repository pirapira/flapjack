import Flapjack.Semantics
import Flapjack.PanMemoryModel

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

/-! Target-supplied byte-addressed operations for structured source memory.

    Structured memory may contain records, but Pancake's sub-word operations
    are defined only on word cells.  The access record therefore makes a
    non-word cell fail instead of silently treating it as a scalar. -/
structure PanValueMemoryAccess (α : Type u) where
  domain : α → Bool
  readWord : (α → Bool) → (α → Option (PanValue α)) → α → α → Option (PanValue α)
  readByte : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  read16 : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  read32 : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  storeWord : (α → Bool) → (α → Option (PanValue α)) → α → α → PanValue α →
    Option (α → Option (PanValue α))
  storeByte : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  store16 : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  store32 : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  /-- Shared-memory operations are separate from ordinary source-memory
      operations.  The callback may ignore the source memory when it is
      backed by an external FFI oracle. -/
  sharedRead : (α → Option (PanValue α)) → α → OpSize → α → Option (PanValue α)
  sharedStore : (α → Option (PanValue α)) → α → OpSize → α → PanValue α →
    Option (α → Option (PanValue α))

def panValueWordMemory (memory : α → Option (PanValue α)) : α → Option α :=
  fun address => match memory address with
    | some (.word value) => some value
    | _ => none

def panValueMemoryAccessOfModel [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3] (model : PanMemoryModel α)
    (domain : α → Bool := fun _ => true)
    (sharedDomain : α → Bool := domain) : PanValueMemoryAccess α :=
  { domain := domain
    readWord := fun _ memory _ address =>
      if domain address then memory address else none
    storeWord := fun _ memory _ address value =>
      if domain address then
        some (fun current => if current == address then some value else memory current)
      else none
    readByte := fun _ memory bytesInWord address =>
      panModelReadByte model domain (panValueWordMemory memory)
        bytesInWord address false
    read16 := fun _ memory bytesInWord address =>
      if model.aligned 2 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then do
          let cell ← memory alignedAddress
          let .word cell := cell | none
          pure (model.wordOfBytes false
            [model.getByte bytesInWord address cell false,
             model.getByte bytesInWord (address + 1) cell false])
        else none
      else none
    read32 := fun _ memory bytesInWord address =>
      panModelRead32 model domain (panValueWordMemory memory)
        bytesInWord address false
    storeByte := fun _ memory bytesInWord address value => do
      let alignedAddress := model.byteAlign bytesInWord address
      if domain alignedAddress then
        let cell ← memory alignedAddress
        let .word cell := cell | none
        let updated := model.setByte bytesInWord address value cell false
        pure (fun current =>
          if current == alignedAddress then some (.word updated) else memory current)
      else none
    store16 := fun _ memory bytesInWord address value => do
      if model.aligned 2 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then
          let cell ← memory alignedAddress
          let .word cell := cell | none
          let cell0 := model.setByte bytesInWord address
            (model.getByte bytesInWord 0 value false) cell false
          let cell1 := model.setByte bytesInWord (address + 1)
            (model.getByte bytesInWord 1 value false) cell0 false
          pure (fun current =>
            if current == alignedAddress then some (.word cell1) else memory current)
        else none
      else none
    store32 := fun _ memory bytesInWord address value => do
      if model.aligned 4 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then
          let cell ← memory alignedAddress
          let .word cell := cell | none
          let cell0 := model.setByte bytesInWord address
            (model.getByte bytesInWord 0 value false) cell false
          let cell1 := model.setByte bytesInWord (address + 1)
            (model.getByte bytesInWord 1 value false) cell0 false
          let cell2 := model.setByte bytesInWord (address + 2)
            (model.getByte bytesInWord 2 value false) cell1 false
          let cell3 := model.setByte bytesInWord (address + 3)
            (model.getByte bytesInWord 3 value false) cell2 false
          pure (fun current =>
            if current == alignedAddress then some (.word cell3) else memory current)
        else none
      else none
    sharedRead := fun memory bytesInWord size address =>
      match size with
      | .opW => (panModelReadWord sharedDomain (panValueWordMemory memory) address).map .word
      | .op8 => (panModelReadByte model sharedDomain (panValueWordMemory memory)
          bytesInWord address false).map .word
      | .op16 => if model.aligned 2 address then
          let alignedAddress := model.byteAlign bytesInWord address
          if sharedDomain alignedAddress then do
            let cell ← memory alignedAddress
            let .word cell := cell | none
            pure (.word (model.wordOfBytes false
              [model.getByte bytesInWord address cell false,
               model.getByte bytesInWord (address + 1) cell false]))
          else none
        else none
      | .op32 => (panModelRead32 model sharedDomain (panValueWordMemory memory)
          bytesInWord address false).map .word
    sharedStore := fun memory bytesInWord size address value =>
      match value with
      | .word value => match size with
          | .opW => if sharedDomain address then
              some (fun current =>
                if current == address then some (.word value) else memory current)
            else none
          | .op8 => (panModelStoreByte model sharedDomain (panValueWordMemory memory)
              bytesInWord address value false).map fun wordMemory current =>
                if current == model.byteAlign bytesInWord address then
                  (wordMemory current).map .word
                else memory current
          | .op16 => if model.aligned 2 address then
              let alignedAddress := model.byteAlign bytesInWord address
              if sharedDomain alignedAddress then do
                let cell ← memory alignedAddress
                let .word cell := cell | none
                let cell0 := model.setByte bytesInWord address
                  (model.getByte bytesInWord 0 value false) cell false
                let cell1 := model.setByte bytesInWord (address + 1)
                  (model.getByte bytesInWord 1 value false) cell0 false
                pure (fun current =>
                  if current == alignedAddress then some (.word cell1) else memory current)
              else none
            else none
          | .op32 => (panModelStore32 model sharedDomain (panValueWordMemory memory)
              bytesInWord address value false).map fun wordMemory current =>
                if current == model.byteAlign bytesInWord address then
                  (wordMemory current).map .word
                else memory current
      | .rStruct _ | .nStruct _ _ => none
  }

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
    (baseAddress topAddress bytesInWord : α) :
    (expression : Exp α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValue α)
  | .const value, _ => some (.word value)
  | .var .local name, _ => locals name
  | .var .global name, _ => globals name
  | .rStruct fields, memoryAccess =>
      (evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)).map .rStruct
  | .rField index expression, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields, memoryAccess => do
      let info ← lookupInfo name structs
      let values ← evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
      if panValueFieldsHaveShapes structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      let value ← match memoryAccess with
        | none => memory address
        | some access => access.readWord access.domain memory bytesInWord address
      if isWfShape structs shape && panShapeMatches (panValueShape structs value) shape then
        some value
      else none
  | .load32 address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => do
          let value ← memory address
          match value with
          | .word value => some (.word value)
          | _ => none
      | some access => (access.read32 access.domain memory bytesInWord address).map .word
  | .loadByte address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => do
          let value ← memory address
          match value with
          | .word value => some (.word value)
          | _ => none
      | some access => (access.readByte access.domain memory bytesInWord address).map .word
  | .op operator arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      match values with
      | [.word left, .word right] =>
          some (.word (evalPanBinOp operator left right))
      | _ => none
  | .panOp .mul arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      match values with
      | [.word left, .word right] => some (.word (left * right))
      | _ => none
  | .cmp operator left right, memoryAccess => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right => some (.word (evalPanCmp operator left right))
      | _, _ => none
  | .shift operator left right, memoryAccess => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right =>
          (evalPanShift operator left right).map .word
      | _, _ => none
  | .baseAddr, _ => some (.word baseAddress)
  | .topAddr, _ => some (.word topAddress)
  | .bytesInWord, _ => some (.word bytesInWord)
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
      (expressions : List (Exp α)) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (List (PanValue α))
    | [], _ => some []
    | expression :: expressions, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions (memoryAccess := memoryAccess)
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
      (fields : List (FieldName × Exp α)) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (List (FieldName × PanValue α))
    | [], _ => some []
    | (name, expression) :: fields, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanValueFields structs locals globals memory
          baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
        pure ((name, value) :: values)
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
      Option (List (PanValue α)) :=
  evalPanValueExp.evalPanValueExps structs locals globals memory
    baseAddress topAddress bytesInWord expressions memoryAccess

def updatePanValueMap [BEq γ] (values : γ → Option α)
    (name : γ) (value : α) : γ → Option α :=
  fun current => if current == name then some value else values current

def updatePanValueMemory [BEq α] (memory : α → Option (PanValue α))
    (address : α) (value : PanValue α) : α → Option (PanValue α) :=
  updatePanValueMap memory address value

def panValueStoreWithAccess [BEq α]
    (memory : α → Option (PanValue α)) (bytesInWord address : α)
    (value : PanValue α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (α → Option (PanValue α)) :=
  match memoryAccess with
  | none => some (updatePanValueMemory memory address value)
  | some access => access.storeWord access.domain memory bytesInWord address value

abbrev PanPrimitiveHandler (α : Type u) :=
  PrimOp → List (PanValue α) → Option (PanValue α)

def restorePanValueLocal [BEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) : VarName → Option (PanValue α) :=
  fun current => if current == name then oldValue else locals current

def evalPanValueProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α) :
    (program : Prog α) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α))
  | .skip, _ => some (locals, globals, memory, [])
  | .dec name shape value body, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals memory primitive body
          (memoryAccess := memoryAccess)
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      pure (updatePanValueMap locals name value, globals, memory, [])
  | .assign .global name value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      pure (locals, updatePanValueMap globals name value, memory, [])
  | .primitive name operator arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
      pure (locals, globals, memory, [])
  | .store32 address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.store32 access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .storeByte address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.storeByte access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .return value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      pure (locals, globals, memory, [value])
  | .seq first second, memoryAccess => do
      let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive first (memoryAccess := memoryAccess)
      if result.2.2.2.isEmpty then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 result.2.2.1 primitive second (memoryAccess := memoryAccess)
      else pure result
  | .ite condition thenBranch elseBranch, memoryAccess => do
      let condition ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
      let .word condition := condition | none
      if condition != 0 then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive thenBranch (memoryAccess := memoryAccess)
      else
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive elseBranch (memoryAccess := memoryAccess)
  | .shMemLoad size kind name address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      let value ← match memoryAccess with
        | none => memory address
        | some access => access.sharedRead memory bytesInWord size address
      match kind with
      | .local => pure (updatePanValueMap locals name value, globals, memory, [])
      | .global => pure (locals, updatePanValueMap globals name value, memory, [])
  | .shMemStore size address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.sharedStore memory bytesInWord size address (.word value)
      pure (locals, globals, memory, [])
  | .tick, _ | .annot _ _, _ => some (locals, globals, memory, [])
  | _, _ => none
termination_by program => sizeOf program

def evalPanValueProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals memory (fun _ _ => none) program memoryAccess

inductive PanValueControlResult (α : Type u) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))

def restorePanValueControlLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueControlResult α → PanValueControlResult α
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

def bindPanValueParameters (parameters : List VarName)
    (values : List (PanValue α)) :
    Option (VarName → Option (PanValue α)) :=
  if parameters.length != values.length then none
  else
    some ((parameters.zip values).foldl
      (fun locals (name, value) => updatePanValueMap locals name value)
      (fun _ => none))

def assignPanValueCallResult
    (locals : VarName → Option (PanValue α))
    (destination : Option (VarKind × VarName))
    (values : List (PanValue α)) :
    Option (VarName → Option (PanValue α)) :=
  match destination, values with
  | none, [] => some locals
  | some (.local, name), [value] => some (updatePanValueMap locals name value)
  | _, _ => none

abbrev PanValueFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
      Option (VarName → Option (PanValue α))

def evalPanValueExtCall [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (structs : StructContext) (handler : PanValueFfiHandler α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × (α → Option (PanValue α))) := do
  let configuration ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configuration (memoryAccess := memoryAccess)
  let configurationLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configurationLength (memoryAccess := memoryAccess)
  let array ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord array (memoryAccess := memoryAccess)
  let arrayLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord arrayLength (memoryAccess := memoryAccess)
  let .word configuration := configuration | none
  let .word configurationLength := configurationLength | none
  let .word array := array | none
  let .word arrayLength := arrayLength | none
  let locals ← handler function configuration configurationLength array arrayLength locals
  pure (locals, globals, memory)

/-!
Fuel-bounded structured source semantics for calls, exceptions, and FFI.  This
is the structured-value counterpart of the scalar control-result evaluator in
`Semantics.lean`; unlike the earlier state evaluator, it keeps caller and
callee state separate and propagates matching exception handlers.
-/
mutual
  def evalPanValueCallWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanValueProgWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel calleeLocals globals memory body
          (memoryAccess := memoryAccess)
        match result with
        | .normal _ _ _ => pure (.normal locals globals memory)
        | .returned _ _ _ values =>
            match info with
            | none => pure (.returned locals globals memory values)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals globals memory)
        | .raised _ _ _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanValueProgWithCallsAndFfi structs functions handler
                    baseAddress topAddress bytesInWord fuel
                    (updatePanValueMap locals handlerVariable value) globals memory
                    handlerProgram (memoryAccess := memoryAccess)
                else pure (.raised locals globals memory exception value)
            | _ => pure (.raised locals globals memory exception value)
        | .broke _ _ _ => pure (.broke locals globals memory)
        | .continued _ _ _ => pure (.continued locals globals memory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _ =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess)
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess => do
        let result ← evalPanValueProgWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory first
          (memoryAccess := memoryAccess)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithCallsAndFfi structs functions handler
              baseAddress topAddress bytesInWord fuel locals globals memory second
              (memoryAccess := memoryAccess)
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory thenBranch
            (memoryAccess := memoryAccess)
        else
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory elseBranch
            (memoryAccess := memoryAccess)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess =>
        evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory info function arguments
          (memoryAccess := memoryAccess)
    | fuel + 1, locals, globals, memory,
        .decCall name _ function arguments body, memoryAccess => do
        let result ← evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory
          (some (some (.local, name), none)) function arguments
          (memoryAccess := memoryAccess)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithCallsAndFfi structs functions handler
              baseAddress topAddress bytesInWord fuel locals globals memory body
              (memoryAccess := memoryAccess)
        | result => pure result
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess => do
        let (locals, globals, memory) ← evalPanValueExtCall structs handler
          locals globals memory baseAddress topAddress bytesInWord function
          configuration configurationLength array arrayLength (memoryAccess := memoryAccess)
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory body
            (memoryAccess := memoryAccess)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithCallsAndFfi structs functions handler
                baseAddress topAddress bytesInWord fuel locals globals memory
                (.while conditionExp body) (memoryAccess := memoryAccess)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _ =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _ =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.raised locals globals memory exception value)
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.returned locals globals memory [value])
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        let value ← match memoryAccess with
          | none => memory address
          | some access => match size with
              | .opW => match memoryAccess with
                  | none => memory address
                  | some access => (access.readWord access.domain memory bytesInWord address)
              | .op8 => (access.readByte access.domain memory bytesInWord address).map .word
              | .op16 => (access.read16 access.domain memory bytesInWord address).map .word
              | .op32 => (access.read32 access.domain memory bytesInWord address).map .word
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
        | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => match size with
              | .opW => panValueStoreWithAccess memory bytesInWord address (.word value)
              | .op8 => access.storeByte access.domain memory bytesInWord address value
              | .op16 => access.store16 access.domain memory bytesInWord address value
              | .op32 => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .tick, _ |
        _fuel + 1, locals, globals, memory, .annot _ _, _ =>
        pure (.normal locals globals memory)
    | _, _, _, _, _, _ => none
    termination_by fuel _ _ _ _ _ => fuel
end

/-!
The combined source evaluator with an explicit primitive environment.  The
ordinary combined evaluator above is useful for programs without primitive
instructions; this version is the one used when a compiler correctness
statement includes `Primitive`, because primitive calls may occur inside
declarations, loops, callees, or exception handlers.
-/
mutual
  def evalPanValueCallWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          calleeLocals globals memory body (memoryAccess := memoryAccess)
        match result with
        | .normal _ _ _ => pure (.normal locals globals memory)
        | .returned _ _ _ values =>
            match info with
            | none => pure (.returned locals globals memory values)
            | some (destination, _) => do
                let locals ← assignPanValueCallResult locals destination values
                pure (.normal locals globals memory)
        | .raised _ _ _ exception value =>
            match info with
            | some (_, some (caught, handlerVariable, handlerProgram)) =>
                if caught == exception then
                  evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                    structs functions baseAddress topAddress bytesInWord fuel
                    (updatePanValueMap locals handlerVariable value) globals memory
                    handlerProgram (memoryAccess := memoryAccess)
                else pure (.raised locals globals memory exception value)
            | _ => pure (.raised locals globals memory exception value)
        | .broke _ _ _ => pure (.broke locals globals memory)
        | .continued _ _ _ => pure (.continued locals globals memory)
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _ =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess)
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.normal (updatePanValueMap locals name value) globals memory)
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments, memoryAccess => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess => do
        let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory first (memoryAccess := memoryAccess)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory second (memoryAccess := memoryAccess)
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory thenBranch (memoryAccess := memoryAccess)
        else
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory elseBranch (memoryAccess := memoryAccess)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess =>
        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory info function arguments (memoryAccess := memoryAccess)
    | fuel + 1, locals, globals, memory, .decCall name _ function arguments body,
        memoryAccess => do
        let result ← evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory (some (some (.local, name), none)) function arguments
          (memoryAccess := memoryAccess)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory body (memoryAccess := memoryAccess)
        | result => pure result
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess => do
        let (locals, globals, memory) ← evalPanValueExtCall structs handler
          locals globals memory baseAddress topAddress bytesInWord function
          configuration configurationLength array arrayLength (memoryAccess := memoryAccess)
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory body (memoryAccess := memoryAccess)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory (.while conditionExp body)
                (memoryAccess := memoryAccess)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _ =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _ =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.raised locals globals memory exception value)
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        pure (.returned locals globals memory [value])
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        let value ← match memoryAccess with
          | none => memory address
          | some access => match size with
              | .opW => match memoryAccess with
                  | none => memory address
                  | some access => (access.readWord access.domain memory bytesInWord address)
              | .op8 => (access.readByte access.domain memory bytesInWord address).map .word
              | .op16 => (access.read16 access.domain memory bytesInWord address).map .word
              | .op32 => (access.read32 access.domain memory bytesInWord address).map .word
        match kind with
        | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
        | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => match size with
              | .opW => panValueStoreWithAccess memory bytesInWord address (.word value)
              | .op8 => access.storeByte access.domain memory bytesInWord address value
              | .op16 => access.store16 access.domain memory bytesInWord address value
              | .op32 => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory,
        .tick, _ | _fuel + 1, locals, globals, memory, .annot _ _, _ =>
        pure (.normal locals globals memory)
    termination_by fuel _ _ _ _ _ => fuel
end

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
