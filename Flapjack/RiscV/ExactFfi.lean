import Flapjack.Ffi
import Flapjack.RiscV.Ffi

/-!
# Exact byte-level RISC-V FFI boundary

This module connects the exact CakeML `callFfi` boundary to the small RISC-V
machine model. It is an adapter rather than a second FFI semantics: the
machine supplies byte arrays through the four Word FFI ABI registers, while
`callFfi` remains the source of observable event and terminal outcome behavior.

The adapter uses the ABI emitted by `wordFfiToRiscV`:

* x10 is the configuration pointer and x11 its byte length;
* x12 is the input/output array pointer and x13 its byte length; and
* x14 is the numeric service identifier.

The compact RISC-V memory model is total, so this first boundary does not yet
model the separate CakeML memory-domain failure for an invalid byte address.
Unknown service identifiers are rejected explicitly.
-/

namespace Flapjack.RiscV

structure ExactRiscVFfiState (width : Nat) (σ : Type u) where
  machine : State width
  ffi : FfiState σ

inductive ExactRiscVFfiResult (width : Nat) (σ : Type u) where
  | normal (state : ExactRiscVFfiState width σ)
  | final (state : ExactRiscVFfiState width σ) (event : FfiFinalEvent)
  | error (state : ExactRiscVFfiState width σ)

def exactReadBytes [NeZero width] (state : State width)
    (address : Word width) (length : Nat) : List UInt8 :=
  (List.range length).map (fun offset =>
    UInt8.ofNat (readByte state (byteAddress address offset)).toNat)

def exactWriteBytesAux [NeZero width] (address : Word width)
    (state : State width) (offset : Nat) : List UInt8 → State width
  | [] => state
  | byte :: bytes =>
      exactWriteBytesAux address
        (writeByte state (byteAddress address offset)
          (BitVec.ofNat 8 byte.toNat)) (offset + 1) bytes

def exactWriteBytes [NeZero width] (state : State width)
    (address : Word width) (bytes : List UInt8) : State width :=
  exactWriteBytesAux address state 0 bytes

def lookupWordFfiName (service : Nat) :
    List (FunName × Nat) → Option FunName
  | [] => none
  | (candidate, candidateService) :: services =>
      if service == candidateService then some candidate
      else lookupWordFfiName service services

def exactRiscVFfiCall [NeZero width]
    (context : WordFfiContext) (state : ExactRiscVFfiState width σ)
    (service : Nat) : ExactRiscVFfiResult width σ :=
  match lookupWordFfiName service context.services with
  | none => .error state
  | some function =>
      let machine := state.machine
      let configurationAddress := readRegister machine 10
      let configurationLength := (readRegister machine 11).toNat
      let arrayAddress := readRegister machine 12
      let arrayLength := (readRegister machine 13).toNat
      let configuration := exactReadBytes machine configurationAddress configurationLength
      let bytes := exactReadBytes machine arrayAddress arrayLength
      match callFfi state.ffi (.extCall function) configuration bytes with
      | .returned ffi bytes =>
          let machine := exactWriteBytes machine arrayAddress bytes
          .normal { machine := { machine with pc := nextPc machine }, ffi := ffi }
      | .final event => .final state event

def executeWithExactFfi [NeZero width]
    (context : WordFfiContext) (state : ExactRiscVFfiState width σ) :
    Instruction width → ExactRiscVFfiResult width σ
  | .ecall =>
      exactRiscVFfiCall context state (readRegister state.machine 14).toNat
  | instruction =>
      .normal { state with machine := execute state.machine instruction }

def executeInstructionsWithExactFfi [NeZero width]
    (context : WordFfiContext) (state : ExactRiscVFfiState width σ) :
    List (Instruction width) → ExactRiscVFfiResult width σ
  | [] => .normal state
  | instruction :: instructions =>
      match executeWithExactFfi context state instruction with
      | .normal state => executeInstructionsWithExactFfi context state instructions
      | result => result

theorem lookupWordFfiName_shape :
    lookupWordFfiName 7 [("echo", 7), ("other", 8)] = some "echo" := by
  rfl

theorem executeWithExactFfi_ecall [NeZero width]
    (context : WordFfiContext) (state : ExactRiscVFfiState width σ) :
    executeWithExactFfi context state .ecall =
      exactRiscVFfiCall context state (readRegister state.machine 14).toNat := by
  rfl

theorem executeWithExactFfi_unknown_service [NeZero width]
    (context : WordFfiContext) (state : ExactRiscVFfiState width σ)
    (hservice : lookupWordFfiName
      (readRegister state.machine 14).toNat context.services = none) :
    executeWithExactFfi context state .ecall = .error state := by
  simp [executeWithExactFfi, exactRiscVFfiCall, hservice]

end Flapjack.RiscV
