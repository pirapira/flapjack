import Std

/-!
The first Lean target-model slice for Pancake's RISC-V backend.

The HOL reference is
`HOL/examples/l3-machine-code/riscv/model/riscv.sml`. This file ports the
architectural vocabulary and the executable register/memory primitives used
by later instruction and compiler-correctness layers. It intentionally does
not claim to be the complete RISC-V transition system yet.
-/

namespace Pancake.RiscV

abbrev Word (width : Nat) := BitVec width

inductive AccessType where
  | read
  | write
  deriving DecidableEq, Repr

inductive FetchType where
  | instruction
  | data
  deriving DecidableEq, Repr

inductive Architecture where
  | rv32i
  | rv64i
  | rv128i
  deriving DecidableEq, Repr

def Architecture.width : Architecture → Nat
  | .rv32i => 32
  | .rv64i => 64
  | .rv128i => 128

inductive Privilege where
  | user
  | supervisor
  | hypervisor
  | machine
  deriving DecidableEq, Repr

inductive VMMode where
  | mbare
  | mbb
  | mbbid
  | sv32
  | sv39
  | sv48
  | sv57
  | sv64
  deriving DecidableEq, Repr

inductive ExtStatus where
  | off
  | initial
  | clean
  | dirty
  deriving DecidableEq, Repr

inductive Interrupt where
  | software
  | timer
  deriving DecidableEq, Repr

inductive ExceptionType where
  | fetchMisaligned
  | fetchFault
  | illegalInstr
  | breakpoint
  | loadFault
  | amoMisaligned
  | storeAmoFault
  | uModeEnvCall
  | sModeEnvCall
  | hModeEnvCall
  | mModeEnvCall
  deriving DecidableEq, Repr

structure SynchronousTrap (width : Nat) where
  badAddress : Option (Word width)
  trap : ExceptionType
  deriving Repr

inductive TransferControl (width : Nat) where
  | branchTo (address : Word width)
  | eReturn
  | mReturn
  | trap (trap : SynchronousTrap width)
  deriving Repr

structure State (width : Nat) where
  pc : Word width
  registers : Fin 32 → Word width
  memory : Word width → BitVec 8
  privilege : Privilege
  mode : VMMode

def zeroState (width : Nat) [NeZero width] : State width :=
  { pc := 0
    registers := fun _ => 0
    memory := fun _ => 0
    privilege := .machine
    mode := .mbare }

def aligned (address : Word width) (alignment : Nat) : Bool :=
  alignment ≠ 0 && address.toNat % alignment = 0

def readRegister (state : State width) (register : Fin 32) : Word width :=
  state.registers register

def writeRegister (state : State width) (register : Fin 32) (value : Word width) : State width :=
  if register = 0 then state
  else { state with registers := fun current => if current = register then value else state.registers current }

def readByte (state : State width) (address : Word width) : BitVec 8 :=
  state.memory address

def writeByte (state : State width) (address : Word width) (value : BitVec 8) : State width :=
  { state with memory := fun current => if current = address then value else state.memory current }

def accessAligned (access : AccessType) (address : Word width) (alignment : Nat) :
    Option ExceptionType :=
  if aligned address alignment then none
  else some (match access with
    | .read => .loadFault
    | .write => .storeAmoFault)

theorem zeroState_pc_zero [NeZero width] : (zeroState width).pc = 0 := by
  rfl

theorem writeRegister_zero (state : State width) (value : Word width) :
    writeRegister state 0 value = state := by
  simp [writeRegister]

theorem accessAligned_aligned (access : AccessType) (address : Word width)
    (alignment : Nat) (aligned_address : aligned address alignment = true) :
    accessAligned access address alignment = none := by
  simp [accessAligned, aligned_address]

end Pancake.RiscV
