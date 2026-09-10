import Flapjack.PanSteppedSemantics
import Flapjack.Ffi

/-!
# Stateful FFI semantics for structured Pancake programs

The ordinary `PanValues` evaluator has deliberately pure host handlers.  This
module adds the next CakeML-facing boundary: a stepped evaluator carrying an
explicit `FfiState`.  In particular, `shMemLoad` and `shMemStore` use the
`SharedMem` FFI operations, including their size byte, aligned address checks,
state transition, and terminal `FinalFFI` result.

The source memory map remains the ordinary Pancake memory.  Shared memory is
observable only through the FFI state, as in CakeML.  The byte codec is
explicit because the source evaluator is polymorphic in its word type.
-/

namespace Flapjack

structure PanValueFfiContext (α : Type u) where
  sharedDomain : α → Bool
  byteAlign : α → α
  bigEndian : Bool
  wordToBytes : α → Bool → List UInt8
  wordOfBytes : Bool → List UInt8 → α
  wordToByte : α → UInt8
  byteToWord : UInt8 → α
  valueToNat : α → Nat

def panValueFfiWidth : OpSize → Nat
  | .op8 => 1
  | .opW => 0
  | .op32 => 4
  | .op16 => 2

def panValueFfiSharedAddress (context : PanValueFfiContext α)
    (size : OpSize) (address : α) : α :=
  let width := panValueFfiWidth size
  if width = 0 then address else context.byteAlign address

inductive PanValueFfiSharedResult (α : Type u) (σ : Type v) where
  | loaded (ffi : FfiState σ) (value : α)
  | stored (ffi : FfiState σ)
  | final (ffi : FfiState σ) (event : FfiFinalEvent)

def panValueFfiSharedLoad (context : PanValueFfiContext α)
    (ffi : FfiState σ) (size : OpSize) (address : α) :
    Option (PanValueFfiSharedResult α σ) :=
  let width := panValueFfiWidth size
  let alignedAddress := panValueFfiSharedAddress context size address
  if !context.sharedDomain alignedAddress then none
  else
    match callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat width]
        (context.wordToBytes alignedAddress false) with
    | .returned nextFfi bytes =>
        some (.loaded nextFfi (context.wordOfBytes context.bigEndian bytes))
    | .final event => some (.final ffi event)

def panValueFfiSharedStore (context : PanValueFfiContext α)
    (ffi : FfiState σ) (size : OpSize) (address value : α) :
    Option (PanValueFfiSharedResult α σ) :=
  let width := panValueFfiWidth size
  let alignedAddress := panValueFfiSharedAddress context size address
  if !context.sharedDomain alignedAddress then none
  else
    let payload :=
      if width = 0 then
        context.wordToBytes value false ++ context.wordToBytes alignedAddress false
      else
        (context.wordToBytes value false).take width ++
          context.wordToBytes alignedAddress false
    match callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat width] payload with
    | .returned nextFfi _ => some (.stored nextFfi)
    | .final event => some (.final ffi event)

def panValueFfiReadBytes [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord address : α) :
    Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
      let byte ← access.readByte access.domain memory bytesInWord address
      let rest ← panValueFfiReadBytes access context memory bytesInWord
        (address + 1) length
      pure (context.wordToByte byte :: rest)
termination_by length => length

def panValueFfiWriteBytes [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
  (memory : α → Option (PanValue α)) (bytesInWord address : α) :
    List UInt8 → (α → Option (PanValue α))
  | [] => memory
  | byte :: bytes =>
      let tailMemory := panValueFfiWriteBytes access context memory bytesInWord
        (address + 1) bytes
      match access.storeByte access.domain tailMemory bytesInWord address
          (context.byteToWord byte) with
      | some updatedMemory => updatedMemory
      | none => memory
termination_by bytes => sizeOf bytes

inductive PanValueFfiExtCallResult (α : Type u) (σ : Type v) where
  | returned (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | final (ffi : FfiState σ) (event : FfiFinalEvent)

def panValueFfiExtCall [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α) :
    Option (PanValueFfiExtCallResult α σ) := do
  let configurationBytes ← panValueFfiReadBytes access context memory bytesInWord
    configuration (context.valueToNat configurationLength)
  let arrayBytes ← panValueFfiReadBytes access context memory bytesInWord
    array (context.valueToNat arrayLength)
  match callFfi ffi (.extCall function) configurationBytes arrayBytes with
  | .returned nextFfi bytes =>
      let memory := panValueFfiWriteBytes access context memory bytesInWord array bytes
      pure (.returned memory nextFfi)
  | .final event => pure (.final ffi event)

inductive PanValueFfiControlResult (α : Type u) (σ : Type v) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (exception : ExceptionId) (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | finalFfi (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (event : FfiFinalEvent)

abbrev PanValueFfiSteppedResult (α : Type u) (σ : Type v) :=
  PanValueFfiControlResult α σ × Nat

abbrev PanValueStatefulFfiHandler (α : Type u) (σ : Type v) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) → FfiState σ →
      Option ((VarName → Option (PanValue α)) × FfiState σ)

/-! Bare-metal accelerator calls may update the Pancake memory map as well as
    the local environment and FFI state.  This is intentionally separate from
    `PanValueStatefulFfiHandler`: the latter models CakeML's ordinary FFI
    boundary, while this handler models an instruction-like target extension
    such as a ZisK accelerator. -/
abbrev PanValueMemoryFfiHandler (α : Type u) (σ : Type v) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
    (α → Option (PanValue α)) → FfiState σ →
      Option ((VarName → Option (PanValue α)) ×
        (α → Option (PanValue α)) × FfiState σ)

def restorePanValueFfiLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueFfiControlResult α σ → PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (restorePanValueLocal locals name oldValue) globals memory ffi
  | .returned locals globals memory ffi values =>
      .returned (restorePanValueLocal locals name oldValue) globals memory ffi values
  | .raised locals globals memory ffi exception value =>
      .raised (restorePanValueLocal locals name oldValue) globals memory ffi exception value
  | .broke locals globals memory ffi =>
      .broke (restorePanValueLocal locals name oldValue) globals memory ffi
  | .continued locals globals memory ffi =>
      .continued (restorePanValueLocal locals name oldValue) globals memory ffi
  | .finalFfi locals globals memory ffi event =>
      .finalFfi (restorePanValueLocal locals name oldValue) globals memory ffi event

mutual
  def evalPanValueFfiCallSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        FfiState σ → Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      (contracts : Option PanValueCallContracts := none) →
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
      Option (PanValueFfiSteppedResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, info, function, arguments, memoryAccess,
        contracts, memoryHandler => do
        let (values, argumentSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← if panValueParametersValid structs contracts function values then
          bindPanValueParameters parameters values
        else none
        let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match result with
        | .normal _ _ _ _ => none
        | .returned _ calleeGlobals calleeMemory calleeFfi values =>
            if panValueReturnValid structs contracts function values &&
                panValueValuesWithinLimit structs values then
              match info with
              | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory calleeFfi values,
                  argumentSteps + steps)
              | some (destination, _) => do
                  let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                    destination values
                    (structs := structs)
                  pure (.normal locals globals calleeMemory calleeFfi,
                    argumentSteps + steps)
            else none
        | .raised _ calleeGlobals calleeMemory calleeFfi exception value =>
            if panValueExceptionValid structs contracts exception value &&
                panValuePayloadWithinLimit structs value then
              match info with
              | some (_, some (caught, handlerVariable, handlerProgram)) =>
                  if caught == exception then
                    if panValueHandlerValid structs contracts locals handlerVariable value then
                      let (handlerResult, handlerSteps) ← evalPanValueFfiProgSteps context
                        primitive handler structs functions baseAddress topAddress bytesInWord fuel
                        (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                        calleeFfi handlerProgram
                        (memoryAccess := memoryAccess) (contracts := contracts)
                        (memoryHandler := memoryHandler)
                      pure (handlerResult, argumentSteps + steps + handlerSteps)
                    else none
                  else
                    pure (.raised (fun _ => none) calleeGlobals calleeMemory calleeFfi exception value,
                      argumentSteps + steps)
              | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory calleeFfi exception value,
                  argumentSteps + steps)
            else none
        | .broke _ _ _ _ | .continued _ _ _ _ => none
        | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
            pure (.finalFfi (fun _ => none) calleeGlobals calleeMemory calleeFfi event,
              argumentSteps + steps)
    termination_by fuel _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiProgSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        FfiState σ → (program : Prog α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      (contracts : Option PanValueCallContracts := none) →
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
      Option (PanValueFfiSteppedResult α σ)
    | 0, _, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, ffi, .skip, _, _, _ =>
        some (.normal locals globals memory ffi, 1)
    | fuel + 1, locals, globals, memory, ffi,
        .dec name shape value body, memoryAccess, contracts, memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
            baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
            globals memory ffi body
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler)
          pure (restorePanValueFfiLocal name oldValue result, valueSteps + steps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .local name value, memoryAccess, _contracts, _memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory ffi,
            valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .global name value, memoryAccess, _contracts, _memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory ffi,
            valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi,
        .primitive name operator arguments, memoryAccess, _contracts, _memoryHandler => do
        let (values, valueSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory ffi, valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi, .store address value, memoryAccess,
        _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, ffi,
        .store32 address value, memoryAccess, _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
    | _fuel + 1, locals, globals, memory, ffi,
        .storeByte address value, memoryAccess, _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
    | fuel + 1, locals, globals, memory, ffi, .seq first second, memoryAccess,
        contracts, memoryHandler => do
        let (firstResult, firstSteps) ← evalPanValueFfiProgSteps context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi first
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match firstResult with
        | .normal locals globals memory ffi =>
            let (secondResult, secondSteps) ← evalPanValueFfiProgSteps context primitive handler
              structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
              second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (secondResult, firstSteps + secondSteps + 1)
        | result => pure (result, firstSteps + 1)
    | _fuel + 1, locals, globals, memory, ffi,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        let (result, steps) ←
          if condition != 0 then
            evalPanValueFfiProgSteps context primitive handler structs functions
              baseAddress topAddress bytesInWord _fuel locals globals memory ffi thenBranch
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
          else
            evalPanValueFfiProgSteps context primitive handler structs functions
              baseAddress topAddress bytesInWord _fuel locals globals memory ffi elseBranch
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
        pure (result, conditionSteps + steps + 1)
    | fuel + 1, locals, globals, memory, ffi,
        .call info function arguments, memoryAccess, contracts, memoryHandler => do
        let (result, steps) ← evalPanValueFfiCallSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        pure (result, steps + 1)
    | fuel + 1, locals, globals, memory, ffi,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (callResult, callSteps) ← evalPanValueFfiCallSteps context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
          none function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match callResult with
        | .returned _ globals memory ffi [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyResult, bodySteps) ← evalPanValueFfiProgSteps context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) globals memory ffi body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (restorePanValueFfiLocal name oldValue bodyResult,
                callSteps + bodySteps + 1)
            else none
        | .raised _ globals memory ffi exception value =>
            pure (.raised (fun _ => none) globals memory ffi exception value,
              callSteps + 1)
        | _ => none
    | _fuel + 1, locals, globals, memory, ffi,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts, memoryHandler => do
        let (values, expressionSteps) ← evalPanValueExpsCounted structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength]
          (memoryAccess := memoryAccess)
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] := values |
          none
        match memoryHandler with
        | some memoryHandler =>
            let (locals, memory, ffi) ← memoryHandler function configuration
              configurationLength array arrayLength locals memory ffi
            pure (.normal locals globals memory ffi, expressionSteps + 1)
        | none =>
            match memoryAccess with
            | none =>
                let (locals, ffi) ←
                  handler function configuration configurationLength array arrayLength locals ffi
                pure (.normal locals globals memory ffi, expressionSteps + 1)
            | some access =>
                match panValueFfiExtCall access context memory bytesInWord ffi function
                    configuration configurationLength array arrayLength with
                | some (.returned memory ffi) =>
                    pure (.normal locals globals memory ffi, expressionSteps + 1)
                | some (.final ffi event) =>
                    pure (.finalFfi (fun _ => none) globals memory ffi event,
                      expressionSteps + 1)
                | none => none
    | fuel + 1, locals, globals, memory, ffi, .while conditionExp body, memoryAccess,
        contracts, memoryHandler => do
        let (condition, conditionSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory ffi, conditionSteps + 1)
        else
          let (bodyResult, bodySteps) ← evalPanValueFfiProgSteps context primitive handler structs
            functions baseAddress topAddress bytesInWord fuel locals globals memory ffi body
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler)
          match bodyResult with
          | .normal locals globals memory ffi | .continued locals globals memory ffi =>
              let (loopResult, loopSteps) ← evalPanValueFfiProgSteps context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
                (.while conditionExp body)
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (loopResult, conditionSteps + bodySteps + loopSteps + 1)
          | .broke locals globals memory ffi =>
              pure (.normal locals globals memory ffi, conditionSteps + bodySteps + 1)
          | result => pure (result, conditionSteps + bodySteps + 1)
    | _fuel + 1, locals, globals, memory, ffi, .break, _, _, _ =>
        pure (.broke locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .continue, _, _, _ =>
        pure (.continued locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .raise exception value, memoryAccess,
        contracts, _memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueExceptionValid structs contracts exception value &&
            panValuePayloadWithinLimit structs value then
          pure (.raised (fun _ => none) globals memory ffi exception value, valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi, .return value, memoryAccess,
        _contracts, _memoryHandler => do
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValuePayloadWithinLimit structs value then
          pure (.returned (fun _ => none) globals memory ffi [value], valueSteps + 1)
        else none
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        if panValueSharedLoadValid structs locals globals kind name (.word 0) then
          match panValueFfiSharedLoad context ffi size address with
          | some (.loaded nextFfi value) =>
              match kind with
              | .local => pure (.normal (updatePanValueMap locals name (.word value)) globals memory nextFfi,
                  addressSteps + 1)
              | .global => pure (.normal locals (updatePanValueMap globals name (.word value)) memory nextFfi,
                  addressSteps + 1)
          | some (.final nextFfi event) =>
              pure (.finalFfi (fun _ => none) globals memory nextFfi event, addressSteps + 1)
          | some (.stored _) | none => none
        else none
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemStore size address value, memoryAccess, _contracts, _memoryHandler => do
        let (address, addressSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let (value, valueSteps) ← evalPanValueExpCounted structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        match panValueFfiSharedStore context ffi size address value with
        | some (.stored nextFfi) =>
            pure (.normal locals globals memory nextFfi, addressSteps + valueSteps + 1)
        | some (.final nextFfi event) =>
            pure (.finalFfi locals globals memory nextFfi event,
              addressSteps + valueSteps + 1)
        | some (.loaded _ _) | none => none
    | _fuel + 1, locals, globals, memory, ffi, .tick, _, _, _ |
        _fuel + 1, locals, globals, memory, ffi, .annot _ _, _, _, _ =>
        pure (.normal locals globals memory ffi, 1)
    termination_by fuel _ _ _ _ _ _ => fuel
end

/-! The accelerator-style handler is selected before the CakeML byte-array
    path.  Keeping this equation as a theorem makes the dispatch priority
    available to source-to-target proofs instead of relying on an unfolding
    detail of the mutual evaluator. -/
theorem evalPanValueFfiProgSteps_extCall_memoryHandler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : PanValueMemoryFfiHandler α σ)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := access) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hhandler : memoryHandler function configuration configurationLength
      array arrayLength locals memory ffi =
      some (nextLocals, nextMemory, nextFfi)) :
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := access) (contracts := contracts)
      (memoryHandler := some memoryHandler) =
      some (.normal nextLocals globals nextMemory nextFfi, expressionSteps + 1) := by
  simp [evalPanValueFfiProgSteps, hvalues, hhandler]

def evalPanValueFfiProgramSteps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiSteppedResult α σ) :=
  evalPanValueFfiProgSteps context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

structure PanValueFfiProgramState (α : Type u) (σ : Type v) where
  source : PanValueProgramState α
  ffi : FfiState σ

def evalPanValueFfiProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiControlResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let (result, _) ← evalPanValueFfiCallSteps context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, .returned locals globals memory ffi [value] =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory ffi [value])
      else none
  | some _, .returned _ _ _ _ _ => none
  | _, result => some result

/-! Public top-level stateful-FFI evaluator retaining the source-step count.
    The underlying call evaluator already records argument and body steps; this
    wrapper keeps that count at the same declaration/entry boundary as
    `evalPanValueFfiProgram`. -/
def evalPanValueFfiProgramStepped
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiSteppedResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let result ← evalPanValueFfiCallSteps context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, (.returned locals globals memory ffi [value], steps) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory ffi [value], steps)
      else none
  | some _, (.returned _ _ _ _ _, _) => none
  | _, result => some result

theorem evalPanValueFfiProgramStepped_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    (evalPanValueFfiProgramStepped context initial primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler)).map Prod.fst =
      evalPanValueFfiProgram context initial primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) := by
  unfold evalPanValueFfiProgramStepped evalPanValueFfiProgram
  cases hstate : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) with
  | none => simp
  | some state =>
      cases hcall : evalPanValueFfiCallSteps context primitive handler state.structs
          state.functions state.baseAddress state.topAddress state.bytesInWord fuel
          (fun _ => none) state.globals state.memory initial.ffi none entry arguments
          (memoryAccess := memoryAccess)
          (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
            state.parameterShapes))
          (memoryHandler := memoryHandler) with
      | none => simp [hcall]
      | some result =>
          cases result with
          | mk control steps =>
              cases hlookup : lookupInfo entry state.returnShapes with
              | none => simp [hcall, hlookup]
              | some shape =>
                  cases control with
                  | normal locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | returned locals globals memory ffi values =>
                      cases values with
                      | nil => simp [hcall, hlookup]
                      | cons value values =>
                          cases values with
                          | nil => simp [hcall, hlookup]
                          | cons value values => simp [hcall, hlookup]
                  | raised locals globals memory ffi exception value =>
                      simp [hcall, hlookup]
                  | broke locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | continued locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | finalFfi locals globals memory ffi event =>
                      simp [hcall, hlookup]

end Flapjack
