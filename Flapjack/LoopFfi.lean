import Flapjack.Ffi
import Flapjack.LoopSemantics

/-!
# Observable Loop FFI operations

This module ports the FFI-facing part of CakeML's `loopSem` state.  It keeps
the ordinary `LoopState` evaluator small and pure, while exposing the exact
byte-array boundary used by `SharedMem` and `FFI`: domain checks happen before
the oracle call, successful calls update the host state and memory, and
terminal oracle results become `FinalFFI` observations.

The byte codec is supplied by the value model.  This is the same abstraction
as CakeML's polymorphic `word_to_bytes`/`word_of_bytes`; using `UInt8` for the
observable payload avoids conflating bytes with machine words.
-/

namespace Flapjack

structure LoopFfiState (α : Type u) (σ : Type v) where
  locals : Nat → Option α
  globals : α → Option α
  memory : α → Option UInt8
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  byteAlign : α → α
  clock : Nat
  bigEndian : Bool
  baseAddress : α
  topAddress : α
  ffi : FfiState σ
  wordToBytes : α → Bool → List UInt8
  wordOfBytes : Bool → List UInt8 → α
  valueToNat : α → Nat

/-! Exact executable counterpart of CakeML Loop's `dec_clock_def`
    (`loopSemScript.sml:42-43`).  Saturating natural subtraction updates only
    the clock field and leaves every other state component unchanged. -/
def decLoopClock (state : LoopFfiState α σ) : LoopFfiState α σ :=
  { state with clock := state.clock - 1 }

/-! Exact executable counterpart of CakeML Loop's `fix_clock_def`
    (`loopSemScript.sml:46-49`).  The result is preserved while the returned
    state's clock is clamped to the smaller of the old and new clocks. -/
def fixLoopClock (oldState : LoopFfiState α σ)
    (step : β × LoopFfiState α σ) : β × LoopFfiState α σ :=
  let (result, newState) := step
  (result, { newState with
    clock := if oldState.clock < newState.clock then oldState.clock else newState.clock })

inductive LoopFfiResult (α : Type u) (σ : Type v) where
  | normal (state : LoopFfiState α σ)
  | error (state : LoopFfiState α σ)
  | finalFfi (state : LoopFfiState α σ) (event : FfiFinalEvent)

abbrev LoopFfiStep (α : Type u) (σ : Type v) :=
  LoopFfiResult α σ × LoopFfiState α σ

def loopFfiMemWidth : CrepMemOp → Nat
  | .load | .store => 0
  | .load8 | .store8 => 1
  | .load16 | .store16 => 2
  | .load32 | .store32 => 4

def loopFfiSharedOperator : CrepMemOp → FfiShmemOp
  | .load | .load8 | .load16 | .load32 => .mappedRead
  | .store | .store8 | .store16 | .store32 => .mappedWrite

def loopFfiIsLoad : CrepMemOp → Bool
  | .load | .load8 | .load16 | .load32 => true
  | .store | .store8 | .store16 | .store32 => false

def loopFfiClearLocals (state : LoopFfiState α σ) : LoopFfiState α σ :=
  { state with locals := fun _ => none }

def loopFfiLocalsPresent (locals : Nat → Option α) : List Nat → Bool
  | [] => true
  | name :: names => (locals name).isSome && loopFfiLocalsPresent locals names

/-- The `cut_state` performed before CakeML's FFI instruction. -/
def loopFfiCutState (state : LoopFfiState α σ) (live : List Nat) :
    Option (LoopFfiState α σ) :=
  if loopFfiLocalsPresent state.locals live then
    some { state with locals := fun name =>
      if name ∈ live then state.locals name else none }
  else none

def loopFfiUpdateLocal (state : LoopFfiState α σ)
    (name : Nat) (value : α) : LoopFfiState α σ :=
  { state with locals := fun current =>
      if current = name then some value else state.locals current }

def loopFfiUpdateByte [BEq α] (memory : α → Option UInt8)
    (address : α) (value : UInt8) : α → Option UInt8 :=
  fun current => if address == current then some value else memory current

def loopFfiReadBytes [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) : α → Nat → Option (List UInt8)
  | _, 0 => some []
  | address, length + 1 => do
      if !state.memaddrs address then none
      else
        let value ← state.memory address
        let rest ← loopFfiReadBytes state (address + 1) length
        pure (value :: rest)

def loopFfiWriteBytes [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) : α → List UInt8 → Option (LoopFfiState α σ)
  | _, [] => some state
  | address, value :: values => do
      if !state.memaddrs address then none
      else
        let state := { state with
          memory := loopFfiUpdateByte state.memory address value }
        loopFfiWriteBytes state (address + 1) values

def loopFfiEvalExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : LoopFfiState α σ) : LoopExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .lookup address => state.globals address
  | .load address => do
      let address ← loopFfiEvalExp state address
      let bytes ← loopFfiReadBytes state address 1
      pure (state.wordOfBytes state.bigEndian bytes)
  | .op operator [left, right] => do
      let left ← loopFfiEvalExp state left
      let right ← loopFfiEvalExp state right
      pure (evalLoopBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← loopFfiEvalExp state left
      let right ← loopFfiEvalExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← loopFfiEvalExp state left
      let right ← loopFfiEvalExp state right
      pure (evalLoopCmp operator left right)
  | .shift operator left right => do
      let left ← loopFfiEvalExp state left
      let right ← loopFfiEvalExp state right
      evalLoopShift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

def loopFfiByteCount (_state : LoopFfiState α σ) (width : Nat) : List UInt8 :=
  [UInt8.ofNat width]

def loopFfiSharedAddress (state : LoopFfiState α σ)
    (address : α) (width : Nat) : α :=
  if width = 0 then address else state.byteAlign address

def loopFfiSharedAddressValid (state : LoopFfiState α σ)
    (address : α) (width : Nat) : Bool :=
  state.shMemaddrs (loopFfiSharedAddress state address width)

def loopFfiSharedLoad [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : LoopFfiStep α σ :=
  let width := loopFfiMemWidth operator
  let alignedAddress := loopFfiSharedAddress state address width
  match state.locals name with
  | none => (.error state, state)
  | some _ =>
      if !state.shMemaddrs alignedAddress then
        (.error state, state)
      else
        match callFfi state.ffi (.sharedMem (loopFfiSharedOperator operator))
            (loopFfiByteCount state width)
            (state.wordToBytes address false) with
        | .final event =>
            let state := loopFfiClearLocals state
            (.finalFfi state event, state)
        | .returned ffi bytes =>
            let value := state.wordOfBytes false bytes
            let state := loopFfiUpdateLocal { state with ffi := ffi } name value
            (.normal state, state)

/-! Direct source-shaped counterpart of `loopSem$sh_mem_load_def`
    (`loopSemScript.sml:198-215`).  Unlike the Crepe operator adapter above,
    this takes the source byte count directly and preserves the source's
    zero-byte address rule. -/
def loopFfiShMemLoad [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (name : Nat) (address : α) (width : Nat) :
    LoopFfiStep α σ :=
  let alignedAddress := if width = 0 then address else state.byteAlign address
  if !state.shMemaddrs alignedAddress then
    (.error state, state)
  else
    match callFfi state.ffi (.sharedMem .mappedRead)
        (loopFfiByteCount state width)
        (state.wordToBytes (if width = 0 then alignedAddress else address) false) with
    | .final event =>
        let state := loopFfiClearLocals state
        (.finalFfi state event, state)
    | .returned ffi bytes =>
        let value := state.wordOfBytes false bytes
        let state := loopFfiUpdateLocal { state with ffi := ffi } name value
        (.normal state, state)

/-! Direct source-shaped counterpart of `loopSem$sh_mem_store_def`
    (`loopSemScript.sml:217-243`).  For nonzero widths the aligned address is
    used only for the domain check; the FFI payload retains the original
    address, as in CakeML's definition. -/
def loopFfiShMemStore [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (name : Nat) (address : α) (width : Nat) :
    LoopFfiStep α σ :=
  let alignedAddress := if width = 0 then address else state.byteAlign address
  match state.locals name with
  | none => (.error state, state)
  | some value =>
      if !state.shMemaddrs alignedAddress then
        (.error state, state)
      else
        let valueBytes := state.wordToBytes value false
        let addressBytes := state.wordToBytes address false
        let payload := if width = 0 then valueBytes ++ addressBytes
          else valueBytes.take width ++ addressBytes
        match callFfi state.ffi (.sharedMem .mappedWrite)
            (loopFfiByteCount state width) payload with
        | .final event =>
            let state := loopFfiClearLocals state
            (.finalFfi state event, state)
        | .returned ffi _ =>
            let state := { state with ffi := ffi }
            (.normal state, state)

/-! Exact dispatch counterpart of `loopSem$sh_mem_op_def`
    (`loopSemScript.sml:255-262`). -/
def loopFfiShMemOp [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : LoopFfiStep α σ :=
  match operator with
  | .load => loopFfiShMemLoad state name address 0
  | .store => loopFfiShMemStore state name address 0
  | .load8 => loopFfiShMemLoad state name address 1
  | .store8 => loopFfiShMemStore state name address 1
  | .load16 => loopFfiShMemLoad state name address 2
  | .store16 => loopFfiShMemStore state name address 2
  | .load32 => loopFfiShMemLoad state name address 4
  | .store32 => loopFfiShMemStore state name address 4

def loopFfiSharedStore [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : LoopFfiStep α σ :=
  let width := loopFfiMemWidth operator
  let alignedAddress := loopFfiSharedAddress state address width
  match state.locals name with
  | none => (.error state, state)
  | some value =>
      if !state.shMemaddrs alignedAddress then
        (.error state, state)
      else
        let bytes :=
          if width = 0 then
            state.wordToBytes value false ++ state.wordToBytes address false
          else
            (state.wordToBytes value false).take width ++
              state.wordToBytes address false
        match callFfi state.ffi (.sharedMem (loopFfiSharedOperator operator))
            (loopFfiByteCount state width) bytes with
        | .final event =>
            let state := loopFfiClearLocals state
            (.finalFfi state event, state)
        | .returned ffi _ =>
            let state := { state with ffi := ffi }
            (.normal state, state)

def loopFfiSharedMem [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : LoopFfiStep α σ :=
  if loopFfiIsLoad operator then
    loopFfiSharedLoad state operator name address
  else
    loopFfiSharedStore state operator name address

def loopFfiExtCall [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : α) : LoopFfiStep α σ :=
  match loopFfiReadBytes state configuration
      (state.valueToNat configurationLength) with
  | none => (.error state, state)
  | some configurationBytes =>
      match loopFfiReadBytes state array (state.valueToNat arrayLength) with
      | none => (.error state, state)
      | some arrayBytes =>
          match callFfi state.ffi (.extCall function)
              configurationBytes arrayBytes with
          | .final event =>
              let state := loopFfiClearLocals state
              (.finalFfi state event, state)
          | .returned ffi newBytes =>
              match loopFfiWriteBytes { state with ffi := ffi } array newBytes with
              | none => (.error state, state)
              | some state => (.normal state, state)

def loopFfiProgramBoundary [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : LoopFfiState α σ) : LoopProg α → Option (LoopFfiStep α σ)
  | .ffi function configuration configurationLength array arrayLength live => do
      /- CakeML reads the four FFI variables from the pre-cut locals;
         `cut_state` only determines the state used afterwards
         (`loopSemScript.sml:426-428`). -/
      let configuration ← state.locals configuration
      let configurationLength ← state.locals configurationLength
      let array ← state.locals array
      let arrayLength ← state.locals arrayLength
      let cutState ← loopFfiCutState state live
      pure (loopFfiExtCall cutState function configuration configurationLength
        array arrayLength)
  | .shMem operator name address => do
      let address ← loopFfiEvalExp state address
      pure (loopFfiSharedMem state operator name address)
  | _ => none

theorem loopFfiReadBytes_zero [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (address : α) :
    loopFfiReadBytes state address 0 = some [] := by
  rfl

theorem loopFfiProgramBoundary_shMem
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : LoopExp α) (addressValue : α)
    (haddress : loopFfiEvalExp state address = some addressValue) :
    loopFfiProgramBoundary state (.shMem operator name address) =
      some (loopFfiSharedMem state operator name addressValue) := by
  simp [loopFfiProgramBoundary, haddress]

theorem loopFfiProgramBoundary_ffi
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state cutState : LoopFfiState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat) (configurationValue configurationLengthValue
      arrayValue arrayLengthValue : α)
    (hcut : loopFfiCutState state live = some cutState)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength : state.locals configurationLength =
      some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue) :
    loopFfiProgramBoundary state
        (.ffi function configuration configurationLength array arrayLength live) =
      some (loopFfiExtCall cutState function configurationValue
        configurationLengthValue arrayValue arrayLengthValue) := by
  simp [loopFfiProgramBoundary, hcut, hconfiguration, hconfigurationLength,
    harray, harrayLength]

theorem loopFfiSharedLoad_final [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) (event : FfiFinalEvent)
    (hvalid : loopFfiSharedAddressValid state address
      (loopFfiMemWidth operator) = true)
    (hname : ∃ value, state.locals name = some value)
    (horacle : callFfi state.ffi
      (.sharedMem (loopFfiSharedOperator operator))
      (loopFfiByteCount state (loopFfiMemWidth operator))
      (state.wordToBytes address false) = .final event) :
    (loopFfiSharedLoad state operator name address).1 =
      .finalFfi (loopFfiClearLocals state) event := by
  have hvalid' : state.shMemaddrs
      (loopFfiSharedAddress state address (loopFfiMemWidth operator)) = true := by
    simpa [loopFfiSharedAddressValid] using hvalid
  rcases hname with ⟨value, hname⟩
  simp [loopFfiSharedLoad, hname, hvalid', horacle]

theorem loopFfiExtCall_final [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (configurationBytes arrayBytes : List UInt8) (event : FfiFinalEvent)
    (hconfiguration : loopFfiReadBytes state configuration
      (state.valueToNat configurationLength) = some configurationBytes)
    (harray : loopFfiReadBytes state array
      (state.valueToNat arrayLength) = some arrayBytes)
    (horacle : callFfi state.ffi (.extCall function)
      configurationBytes arrayBytes = .final event) :
    (loopFfiExtCall state function configuration configurationLength array arrayLength).1 =
      .finalFfi (loopFfiClearLocals state) event := by
  simp [loopFfiExtCall, hconfiguration, harray, horacle]

end Flapjack
