import Flapjack.Ffi
import Flapjack.Loop

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
  memory : α → Option UInt8
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  byteAlign : α → α
  clock : Nat
  bigEndian : Bool
  ffi : FfiState σ
  wordToBytes : α → Bool → List UInt8
  wordOfBytes : Bool → List UInt8 → α
  valueToNat : α → Nat

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

def loopFfiByteCount (state : LoopFfiState α σ) (width : Nat) : List UInt8 :=
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
  if !state.shMemaddrs alignedAddress then
    (.error state, state)
  else
    match callFfi state.ffi (.sharedMem (loopFfiSharedOperator operator))
        (loopFfiByteCount state width)
        (state.wordToBytes alignedAddress false) with
    | .final event =>
        let state := loopFfiClearLocals state
        (.finalFfi state event, state)
    | .returned ffi bytes =>
        let value := state.wordOfBytes state.bigEndian bytes
        let state := loopFfiUpdateLocal { state with ffi := ffi } name value
        (.normal state, state)

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
            state.wordToBytes value false ++ state.wordToBytes alignedAddress false
          else
            (state.wordToBytes value false).take width ++
              state.wordToBytes alignedAddress false
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

def loopFfiProgramBoundary [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) : LoopProg α → Option (LoopFfiStep α σ)
  | .ffi function configuration configurationLength array arrayLength _ => do
      let configuration ← state.locals configuration
      let configurationLength ← state.locals configurationLength
      let array ← state.locals array
      let arrayLength ← state.locals arrayLength
      pure (loopFfiExtCall state function configuration configurationLength
        array arrayLength)
  | .shMem operator name address => none
  | _ => none

theorem loopFfiReadBytes_zero [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (address : α) :
    loopFfiReadBytes state address 0 = some [] := by
  rfl

theorem loopFfiSharedLoad_final [BEq α] [OfNat α 1] [Add α]
    (state : LoopFfiState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) (event : FfiFinalEvent)
    (hvalid : loopFfiSharedAddressValid state address
      (loopFfiMemWidth operator) = true)
    (horacle : callFfi state.ffi
      (.sharedMem (loopFfiSharedOperator operator))
      (loopFfiByteCount state (loopFfiMemWidth operator))
      (state.wordToBytes (loopFfiSharedAddress state address
        (loopFfiMemWidth operator)) false) = .final event) :
    (loopFfiSharedLoad state operator name address).1 =
      .finalFfi (loopFfiClearLocals state) event := by
  have hvalid' : state.shMemaddrs
      (loopFfiSharedAddress state address (loopFfiMemWidth operator)) = true := by
    simpa [loopFfiSharedAddressValid] using hvalid
  simp [loopFfiSharedLoad, hvalid', horacle]

end Flapjack
