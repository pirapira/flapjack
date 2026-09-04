import Std

/-!
The first Lean target-model slice for Flapjack's RISC-V backend.

The HOL reference is
`HOL/examples/l3-machine-code/riscv/model/riscv.sml`. This file ports the
architectural vocabulary and the executable register/memory primitives used
by later instruction and compiler-correctness layers. It intentionally does
not claim to be the complete RISC-V transition system yet.
-/

namespace Flapjack.RiscV

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

inductive Instruction (width : Nat) where
  | add (destination sourceLeft sourceRight : Fin 32)
  | sub (destination sourceLeft sourceRight : Fin 32)
  | and (destination sourceLeft sourceRight : Fin 32)
  | or (destination sourceLeft sourceRight : Fin 32)
  | xor (destination sourceLeft sourceRight : Fin 32)
  | addi (destination source : Fin 32) (immediate : Word width)
  deriving Repr

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

def ZeroRegister (state : State width) : Prop :=
  readRegister state 0 = 0

def writeRegister (state : State width) (register : Fin 32) (value : Word width) : State width :=
  if register = 0 then state
  else { state with registers := fun current => if current = register then value else state.registers current }

def readByte (state : State width) (address : Word width) : BitVec 8 :=
  state.memory address

def writeByte (state : State width) (address : Word width) (value : BitVec 8) : State width :=
  { state with memory := fun current => if current = address then value else state.memory current }

def nextPc (state : State width) : Word width := state.pc + 4

def execute (state : State width) : Instruction width → State width
  | .add destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft + readRegister state sourceRight)
  | .sub destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft - readRegister state sourceRight)
  | .and destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft &&& readRegister state sourceRight)
  | .or destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft ||| readRegister state sourceRight)
  | .xor destination sourceLeft sourceRight =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state sourceLeft ^^^ readRegister state sourceRight)
  | .addi destination source immediate =>
      writeRegister { state with pc := nextPc state } destination
        (readRegister state source + immediate)

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

theorem execute_pc_advance (state : State width) (instruction : Instruction width) :
    (execute state instruction).pc = state.pc + 4 := by
  cases instruction <;> simp [execute, nextPc, writeRegister] <;> split <;> rfl

theorem execute_addi_zero_preserved (state : State width) (source : Fin 32)
    (immediate : Word width) :
    readRegister (execute state (.addi 0 source immediate)) 0 = readRegister state 0 := by
  simp [execute, nextPc, writeRegister, readRegister]

theorem execute_zeroRegister_preserved [NeZero width] (state : State width)
    (instruction : Instruction width) (zero : ZeroRegister state) :
    ZeroRegister (execute state instruction) := by
  change state.registers 0 = 0 at zero
  cases instruction <;>
    simp [ZeroRegister, execute, nextPc, writeRegister, readRegister] <;>
    split <;> simp_all [eq_comm]

theorem zeroState_zeroRegister [NeZero width] : ZeroRegister (zeroState width) := by
  simp [ZeroRegister, zeroState, readRegister]

end Flapjack.RiscV
