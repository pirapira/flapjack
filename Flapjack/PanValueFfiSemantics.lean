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
        (context.wordToBytes address false) with
    | .returned nextFfi bytes =>
        some (.loaded nextFfi (context.wordOfBytes false bytes))
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
        context.wordToBytes value false ++ context.wordToBytes address false
      else
        (context.wordToBytes value false).take width ++
          context.wordToBytes address false
    match callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat width] payload with
    | .returned nextFfi _ => some (.stored nextFfi)
    | .final event => some (.final ffi event)

/-- Inversion of a successful mapped read: the address passes the shared-memory
    domain guard and `call_FFI` (Lean `callFfi`) returns bytes whose
    `word_of_bytes` image is the observed value. -/
theorem panValueFfiSharedLoad_loaded_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address : α) (nextFfi : FfiState σ) (value : α)
    (h : panValueFfiSharedLoad context ffi size address = some (.loaded nextFfi value)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    ∃ bytes,
      callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
          (context.wordToBytes address false) = .returned nextFfi bytes ∧
      value = context.wordOfBytes false bytes := by
  simp only [panValueFfiSharedLoad] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hval
        exact ⟨hdom, bytes, by simp only [hffi], hval.symm⟩
    | final event =>
        rw [hcall] at h
        simp at h
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a terminal mapped read. -/
theorem panValueFfiSharedLoad_final_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address : α) (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (h : panValueFfiSharedLoad context ffi size address = some (.final nextFfi event)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    nextFfi = ffi ∧
    callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) = .final event := by
  simp only [panValueFfiSharedLoad] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedRead) [UInt8.ofNat (panValueFfiWidth size)]
        (context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp at h
    | final event' =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hev
        exact ⟨hdom, hffi.symm, by simp only [hev]⟩
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a successful mapped write: the address passes the domain guard
    and the `SharedMem MappedWrite` send returns normally, updating the ffi. -/
theorem panValueFfiSharedStore_stored_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address value : α) (nextFfi : FfiState σ)
    (h : panValueFfiSharedStore context ffi size address value = some (.stored nextFfi)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    ∃ bytes,
      callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
          (if panValueFfiWidth size = 0 then
              context.wordToBytes value false ++ context.wordToBytes address false
            else
              (context.wordToBytes value false).take (panValueFfiWidth size) ++
                context.wordToBytes address false) = .returned nextFfi bytes := by
  simp only [panValueFfiSharedStore] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi
        exact ⟨hdom, bytes, by simp only [hffi]⟩
    | final event =>
        rw [hcall] at h
        simp at h
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

/-- Inversion of a terminal mapped write. -/
theorem panValueFfiSharedStore_final_inv
    (context : PanValueFfiContext α) (ffi : FfiState σ) (size : OpSize)
    (address value : α) (nextFfi : FfiState σ) (event : FfiFinalEvent)
    (h : panValueFfiSharedStore context ffi size address value = some (.final nextFfi event)) :
    context.sharedDomain (panValueFfiSharedAddress context size address) = true ∧
    nextFfi = ffi ∧
    callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) = .final event := by
  simp only [panValueFfiSharedStore] at h
  by_cases hdom : context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · rw [hdom] at h
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hcall : callFfi ffi (.sharedMem .mappedWrite) [UInt8.ofNat (panValueFfiWidth size)]
        (if panValueFfiWidth size = 0 then
            context.wordToBytes value false ++ context.wordToBytes address false
          else
            (context.wordToBytes value false).take (panValueFfiWidth size) ++
              context.wordToBytes address false) with
    | returned returnedFfi bytes =>
        rw [hcall] at h
        simp at h
    | final event' =>
        rw [hcall] at h
        simp only [Option.some.injEq] at h
        injection h with hffi hev
        exact ⟨hdom, hffi.symm, by simp only [hev]⟩
  · have hb : context.sharedDomain (panValueFfiSharedAddress context size address) = false := by
      cases hval : context.sharedDomain (panValueFfiSharedAddress context size address) <;>
        simp_all
    rw [hb] at h
    simp at h

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

/-! The successful byte-array ExtCall path preserves the incoming Cake FFI
    trace.  This is the concrete FFI premise used by the evaluator-level
    `evaluate_io_events_mono` bridge below. -/
theorem panValueFfiExtCall_returned_ioEvents_prefix
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (hcall : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength =
      some (.returned nextMemory nextFfi)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  unfold panValueFfiExtCall at hcall
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => simp [hconfiguration] at hcall
  | some configurationBytes =>
      cases harray : panValueFfiReadBytes access context memory bytesInWord
          array (context.valueToNat arrayLength) with
      | none => simp [hconfiguration, harray] at hcall
      | some arrayBytes =>
          cases hffi : callFfi ffi (.extCall function) configurationBytes arrayBytes with
          | final event => simp [hconfiguration, harray, hffi] at hcall
          | returned returnedFfi returnedBytes =>
              simp [hconfiguration, harray, hffi] at hcall
              rcases hcall with ⟨_, rfl⟩
              exact callFfi_return_ioEvents_prefix ffi (.extCall function)
                configurationBytes arrayBytes returnedFfi returnedBytes hffi

/-- Inversion of a successful `panValueFfiExtCall` outcome: the two argument
    reads and the `call_FFI` returned result, with the write-back memory. -/
theorem panValueFfiExtCall_returned_inv
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (h : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength =
      some (.returned nextMemory nextFfi)) :
    ∃ configurationBytes arrayBytes bytes,
      panValueFfiReadBytes access context memory bytesInWord configuration
          (context.valueToNat configurationLength) = some configurationBytes ∧
      panValueFfiReadBytes access context memory bytesInWord array
          (context.valueToNat arrayLength) = some arrayBytes ∧
      callFfi ffi (.extCall function) configurationBytes arrayBytes =
        .returned nextFfi bytes ∧
      nextMemory = panValueFfiWriteBytes access context memory bytesInWord
        array bytes := by
  unfold panValueFfiExtCall at h
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => simp [hconfiguration] at h
  | some configurationBytes =>
      cases harray : panValueFfiReadBytes access context memory bytesInWord
          array (context.valueToNat arrayLength) with
      | none => simp [hconfiguration, harray] at h
      | some arrayBytes =>
          cases hffi : callFfi ffi (.extCall function) configurationBytes arrayBytes with
          | final event => simp [hconfiguration, harray, hffi] at h
          | returned returnedFfi bytes =>
              simp [hconfiguration, harray, hffi] at h
              rcases h with ⟨hmem, hffiEq⟩
              exact ⟨configurationBytes, arrayBytes, bytes, rfl, rfl,
                by rw [← hffiEq]; exact hffi, hmem.symm⟩

inductive PanValueFfiControlResult (α : Type u) (σ : Type v) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
  | error (locals globals : VarName → Option (PanValue α))
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
  | .error locals globals memory ffi =>
      .error (restorePanValueLocal locals name oldValue) globals memory ffi
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

/-- Result of a `local` assignment leaf.  HOL's `Assign` returns `SOME Error`
with the unchanged state both when the source expression does not evaluate and
when `is_valid_value` rejects the evaluated value; this helper returns the
explicit `.error` control result in both cases. -/
def panValueAssignLocalResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueAssignmentValid structs locals globals .local name value then
        some (.normal (updatePanValueMap locals name value) globals memory ffi, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of a `global` assignment leaf; see `panValueAssignLocalResult`. -/
def panValueAssignGlobalResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueAssignmentValid structs locals globals .global name value then
        some (.normal locals (updatePanValueMap globals name value) memory ffi, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Acceptance test for the `Dec` leaf.  HOL's `Dec` returns `SOME Error` with
the unchanged state both when the initialiser does not evaluate and when its
shape does not match; this helper returns the accepted value with its step count
in the successful case and `none` otherwise. -/
def panValueDecAccepted
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape) :
    Option (PanValue α × Nat) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => none
  | some (evaluated, valueSteps) =>
      if panShapeMatches (panValueShape structs evaluated) shape then
        some (evaluated, valueSteps)
      else none

/-- Uncounted acceptance test for `Dec`, used by the clocked evaluators. -/
def panValueDecAcceptedValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape) :
    Option (PanValue α) :=
  match evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => none
  | some evaluated =>
      if panShapeMatches (panValueShape structs evaluated) shape then some evaluated else none

/-- Condition value of an `If`.  HOL evaluates the condition and requires a
word, returning `SOME Error` with the unchanged state otherwise. -/
def panValueIteConditionValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (condition : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option α :=
  match evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      condition (memoryAccess := memoryAccess) with
  | some (.word value) => some value
  | _ => none

/-- Result of the `Primitive` leaf.  HOL returns `SOME Error` with the unchanged
state when the arguments do not evaluate, when `pan_primop` returns `NONE`, or
when `is_valid_value` rejects the result; the successful case updates the
destination variable. -/
def panValuePrimitiveResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (primitive : PanPrimitiveHandler α) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpsCounted structs locals globals memory baseAddress topAddress bytesInWord
      arguments (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (values, valueSteps) =>
      match primitive operator values with
      | none => some (.error locals globals memory ffi, valueSteps + 1)
      | some value =>
          match locals name with
          | none => some (.error locals globals memory ffi, valueSteps + 1)
          | some oldValue =>
              if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
                some (.normal (updatePanValueMap locals name value) globals memory ffi,
                  valueSteps + 1)
              else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of the `Store` leaf.  HOL's `Store` returns `SOME Error` with the
unchanged state when either operand does not evaluate, when the address is not a
word, or when the memory store fails. -/
def panValueStoreResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      address (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
          value (memoryAccess := memoryAccess) with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address with
          | .word address =>
              match panValueStoreWithAccess memory bytesInWord address value memoryAccess with
              | some memory =>
                  some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
              | none =>
                  some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _ => some (.error locals globals memory ffi, addressSteps + valueSteps + 1)

/-- Result of the `Store32` leaf; see `panValueStoreResult`. -/
def panValueStore32Result
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      address (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
          value (memoryAccess := memoryAccess) with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match memoryAccess with
              | none =>
                  some (.normal locals globals
                    (updatePanValueMemory memory address (.word value)) ffi,
                    addressSteps + valueSteps + 1)
              | some access =>
                  match access.store32 access.domain memory bytesInWord address value with
                  | some memory =>
                      some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
                  | none =>
                      some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Result of the `StoreByte` leaf; see `panValueStoreResult`. -/
def panValueStoreByteResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      address (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
          value (memoryAccess := memoryAccess) with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match memoryAccess with
              | none =>
                  some (.normal locals globals
                    (updatePanValueMemory memory address (.word value)) ffi,
                    addressSteps + valueSteps + 1)
              | some access =>
                  match access.storeByte access.domain memory bytesInWord address value with
                  | some memory =>
                      some (.normal locals globals memory ffi, addressSteps + valueSteps + 1)
                  | none =>
                      some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Result of the `ShMemLoad` leaf.  HOL returns `SOME Error` with the unchanged
state when the address does not evaluate to a word, when the destination is not a
word-valued variable, or when the shared load fails. -/
def panValueShMemLoadResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      address (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match address with
      | .word address =>
          if panValueSharedLoadValid structs locals globals kind name (.word 0) then
            match panValueFfiSharedLoad context ffi size address with
            | some (.loaded nextFfi value) =>
                match kind with
                | .local =>
                    some (.normal (updatePanValueMap locals name (.word value)) globals memory
                      nextFfi, addressSteps + 1)
                | .global =>
                    some (.normal locals (updatePanValueMap globals name (.word value)) memory
                      nextFfi, addressSteps + 1)
            | some (.final nextFfi event) =>
                some (.finalFfi (fun _ => none) globals memory nextFfi event, addressSteps + 1)
            | some (.stored _) | none =>
                some (.error locals globals memory ffi, addressSteps + 1)
          else some (.error locals globals memory ffi, addressSteps + 1)
      | _ => some (.error locals globals memory ffi, addressSteps)

/-- Result of the `ShMemStore` leaf; see `panValueShMemLoadResult`. -/
def panValueShMemStoreResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (size : OpSize) (address value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α)) : Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      address (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (address, addressSteps) =>
      match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
          value (memoryAccess := memoryAccess) with
      | none => some (.error locals globals memory ffi, addressSteps)
      | some (value, valueSteps) =>
          match address, value with
          | .word address, .word value =>
              match panValueFfiSharedStore context ffi size address value with
              | some (.stored nextFfi) =>
                  some (.normal locals globals memory nextFfi, addressSteps + valueSteps + 1)
              | some (.final nextFfi event) =>
                  some (.finalFfi locals globals memory nextFfi event,
                    addressSteps + valueSteps + 1)
              | some (.loaded _ _) | none =>
                  some (.error locals globals memory ffi, addressSteps + valueSteps + 1)
          | _, _ => some (.error locals globals memory ffi, addressSteps + valueSteps)

/-- Counted condition value of an `If`, used by the executable leaf evaluator. -/
def panValueIteCondition
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (condition : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (α × Nat) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      condition (memoryAccess := memoryAccess) with
  | some (.word value, steps) => some (value, steps)
  | _ => none

/-- Resolve the callee body and locals for a call.  HOL returns `SOME Error`
with the unchanged state when the function is missing or the arguments are
invalid. -/
def panValueCallTarget
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (contracts : Option PanValueCallContracts)
    (function : FunName) (functions : List (FunName × List VarName × Prog α))
    (values : List (PanValue α)) :
    Option (Prog α × (VarName → Option (PanValue α))) :=
  match lookupPanFunction function functions with
  | none => none
  | some (parameters, body) =>
      if panValueParametersValid structs contracts function values then
        match bindPanValueParameters parameters values with
        | some calleeLocals => some (body, calleeLocals)
        | none => none
      else none

/-- Counted evaluation of a call's argument list.  HOL returns `SOME Error`
with the unchanged state when this fails. -/
def panValueCallArguments
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (arguments : List (Exp α)) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (List (PanValue α) × Nat) :=
  evalPanValueExpsCounted structs locals globals memory baseAddress topAddress bytesInWord
    arguments (memoryAccess := memoryAccess)

/-- Uncounted evaluation of a call's argument list; the clocked counterpart of
`panValueCallArguments`. -/
def panValueCallArgumentsValue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (arguments : List (Exp α)) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (List (PanValue α)) :=
  evalPanValueExps structs locals globals memory baseAddress topAddress bytesInWord
    arguments (memoryAccess := memoryAccess)

/-- Result of the `Return` leaf.  HOL returns `SOME Error` with the unchanged
state when the expression fails to evaluate or the payload exceeds the limit. -/
def panValueReturnResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValuePayloadWithinLimit structs value then
        some (.returned (fun _ => none) globals memory ffi [value], valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

/-- Result of the `Raise` leaf.  HOL returns `SOME Error` with the unchanged
state when the expression fails to evaluate or the exception shape/size is
invalid. -/
def panValueRaiseResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α)) (memory : α → Option (PanValue α))
    (ffi : FfiState σ) (contracts : Option PanValueCallContracts)
    (exception : VarName) (value : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)) :
    Option (PanValueFfiSteppedResult α σ) :=
  match evalPanValueExpCounted structs locals globals memory baseAddress topAddress bytesInWord
      value (memoryAccess := memoryAccess) with
  | none => some (.error locals globals memory ffi, 0)
  | some (value, valueSteps) =>
      if panValueExceptionValid structs contracts exception value &&
          panValuePayloadWithinLimit structs value then
        some (.raised (fun _ => none) globals memory ffi exception value, valueSteps + 1)
      else some (.error locals globals memory ffi, valueSteps + 1)

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
        (panValueCallArguments structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun argumentPair => do
            let (values, argumentSteps) := argumentPair
            (panValueCallTarget structs contracts function functions values).elim
              (some (.error locals globals memory ffi, argumentSteps))
              (fun callTarget => do
                let (body, calleeLocals) := callTarget
                let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
                  baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
                -- HOL returns `SOME Error` preserving the callee state's locals for
                -- NONE/Break/Continue, and empties them only in the catch-all
                -- (`SOME Error`/TimeOut) clause.
                match result with
                | .normal calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    some (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
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
                    else some (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
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
                | .broke calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    pure (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .continued calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    pure (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .error _ calleeGlobals calleeMemory calleeFfi =>
                    pure (.error (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                    pure (.finalFfi (fun _ => none) calleeGlobals calleeMemory calleeFfi event,
                      argumentSteps + steps)))
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
        .dec name shape value body, memoryAccess, contracts, memoryHandler =>
        (panValueDecAccepted structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape).elim
          (some (.error locals globals memory ffi, 0))
          (fun accepted => do
            let oldValue := locals name
            let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name accepted.1)
              globals memory ffi body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (restorePanValueFfiLocal name oldValue result, accepted.2 + steps + 1))
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .local name value, memoryAccess, _contracts, _memoryHandler =>
        panValueAssignLocalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .global name value, memoryAccess, _contracts, _memoryHandler =>
        panValueAssignGlobalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .primitive name operator arguments, memoryAccess, _contracts, _memoryHandler =>
        panValuePrimitiveResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi name operator arguments memoryAccess primitive
    | _fuel + 1, locals, globals, memory, ffi, .store address value, memoryAccess,
        _contracts, _memoryHandler =>
        panValueStoreResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .store32 address value, memoryAccess, _contracts, _memoryHandler =>
        panValueStore32Result structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .storeByte address value, memoryAccess, _contracts, _memoryHandler =>
        panValueStoreByteResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
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
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler =>
        (panValueIteCondition structs baseAddress topAddress bytesInWord locals globals memory
          condition memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun conditionPair => do
            let (condition, conditionSteps) := conditionPair
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
            pure (result, conditionSteps + steps + 1))
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
            else some (.error (fun _ => none) globals memory ffi, callSteps + 1)
        | .raised _ globals memory ffi exception value =>
            pure (.raised (fun _ => none) globals memory ffi exception value,
              callSteps + 1)
        | .finalFfi _ globals memory ffi event =>
            pure (.finalFfi (fun _ => none) globals memory ffi event,
              callSteps + 1)
        | .error calleeLocals globals memory ffi =>
            pure (.error calleeLocals globals memory ffi, callSteps + 1)
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
            match memoryHandler function configuration configurationLength array arrayLength
                locals memory ffi with
            | some (locals, memory, ffi) =>
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
        contracts, memoryHandler =>
        (panValueIteCondition structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun conditionPair => do
            let (conditionValue, conditionSteps) := conditionPair
            if conditionValue == 0 then
              pure (.normal locals globals memory ffi, conditionSteps + 1)
            else
              let (bodyResult, bodySteps) ← evalPanValueFfiProgSteps context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
                body (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              match bodyResult with
              | .normal locals globals memory ffi | .continued locals globals memory ffi =>
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps context primitive handler
                    structs functions baseAddress topAddress bytesInWord fuel locals globals memory
                    ffi (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler)
                  pure (loopResult, conditionSteps + bodySteps + loopSteps + 1)
              | .broke locals globals memory ffi =>
                  pure (.normal locals globals memory ffi, conditionSteps + bodySteps + 1)
              | result => pure (result, conditionSteps + bodySteps + 1))
    | _fuel + 1, locals, globals, memory, ffi, .break, _, _, _ =>
        pure (.broke locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .continue, _, _, _ =>
        pure (.continued locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .raise exception value, memoryAccess,
        contracts, _memoryHandler =>
        panValueRaiseResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          contracts exception value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi, .return value, memoryAccess,
        _contracts, _memoryHandler =>
        panValueReturnResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler =>
        panValueShMemLoadResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size kind name address memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemStore size address value, memoryAccess, _contracts, _memoryHandler =>
        panValueShMemStoreResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size address value memoryAccess
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

theorem evalPanValueFfiProgSteps_extCall_returned_ioEvents_prefix
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
    (contracts : Option PanValueCallContracts)
    (access : PanValueMemoryAccess α)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := some access) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := some access) (contracts := contracts)
      (memoryHandler := none) =
      some (.normal nextLocals globals nextMemory nextFfi, expressionSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, hvalues] at hresult
  cases hcall : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength with
  | none => simp [hcall] at hresult
  | some result =>
      cases result with
      | returned returnedMemory returnedFfi =>
          simp [hcall] at hresult
          rcases hresult with ⟨_, ⟨_, hffi⟩⟩
          rw [← hffi]
          exact panValueFfiExtCall_returned_ioEvents_prefix access context memory
            bytesInWord ffi function configuration configurationLength array arrayLength
            returnedMemory returnedFfi hcall
      | final event => simp [hcall] at hresult

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

/-! Exact source callers carry the Cake memory operations as data rather than
    relying on the optional compatibility argument below. -/
structure PanValueFfiExactProgramState (α : Type u) (σ : Type v) where
  legacy : PanValueFfiProgramState α σ
  memoryAccess : PanValueMemoryAccess α

def PanValueFfiExactProgramState.toProgramState
    (state : PanValueFfiExactProgramState α σ) : PanValueFfiProgramState α σ :=
  state.legacy

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

def evalPanValueFfiExactProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiControlResult α σ) :=
  evalPanValueFfiProgram context initial.legacy primitive handler fuel declarations entry
    arguments (memoryAccess := some initial.memoryAccess)
    (memoryHandler := memoryHandler)

theorem evalPanValueFfiExactProgram_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiExactProgram context initial primitive handler fuel declarations entry
        arguments (memoryHandler := memoryHandler) =
      evalPanValueFfiProgram context initial.legacy primitive handler fuel declarations entry
        arguments (memoryAccess := some initial.memoryAccess)
        (memoryHandler := memoryHandler) := by
  rfl

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

/-! The stepped exact entrypoint carries the Cake memory operations in its
    state, just as `evalPanValueFfiExactProgram` does.  In particular, an
    exact caller cannot accidentally select the legacy whole-cell load/store
    fallback by omitting `memoryAccess`. -/
def evalPanValueFfiExactProgramStepped
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    Option (PanValueFfiSteppedResult α σ) :=
  evalPanValueFfiProgramStepped context initial.legacy primitive handler fuel
    declarations entry arguments
    (memoryAccess := some initial.memoryAccess)

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
                  | error locals globals memory ffi =>
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

theorem evalPanValueFfiExactProgramStepped_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    (evalPanValueFfiExactProgramStepped context initial primitive handler fuel
      declarations entry arguments).map Prod.fst =
      evalPanValueFfiExactProgram context initial primitive handler fuel
        declarations entry arguments := by
  exact evalPanValueFfiProgramStepped_fst context initial.legacy primitive handler
    fuel declarations entry arguments
    (memoryAccess := some initial.memoryAccess)

end Flapjack
