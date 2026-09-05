import Flapjack.Stack
import Flapjack.RiscV.Allocator

/-!
# Word-to-Stack spill moves

This is the first executable consumer of the spill locations produced by the
Word allocator.  It ports the essential `wMoveSingle` cases from CakeML's
`word_to_stackScript.sml`: a virtual variable is either represented by a
physical register or by a slot in the current stack frame, and `x31` is used
as the temporary for moves involving stack locations.

The full CakeML pass also lowers every Word instruction and maintains GC
bitmaps.  Those later pieces will build on this total location lookup and its
explicit move cases.
-/

namespace Flapjack.RiscV

structure WordStackConfig where
  locations : NatInfoMap WordLocation
  scratch : Nat
  stackBase : Nat
  addressScratch : Nat := 29
  perf : Bool := false
  frameOffset : Nat := 0
  returnLabel : Nat := 0
  entryLabel : Nat := 0
  handlerLabel : Nat := 0
  deriving Repr

def wordStackLocation (config : WordStackConfig) (name : Nat) :
    Option WordLocation :=
  lookupNatInfo name config.locations

def wordStackOffset (config : WordStackConfig) (slot : Nat) : Nat :=
  config.stackBase + slot

def wordStackMove (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let source ← wordStackLocation config source
  match destination, source with
  | .register destination, .register source =>
      pure (.arith .or destination source source)
  | .register destination, .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))
  | .stack slot, .register source =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))
  | .stack destinationSlot, .stack sourceSlot =>
      pure (.seq (.stackLoad config.scratch
          (wordStackOffset config sourceSlot))
        (.stackStore config.scratch (wordStackOffset config destinationSlot)))

def wordToStackMove (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) :=
  wordStackMove config destination source

def wordStackLoadInst (config : WordStackConfig) (operator : WordMemOp)
    (destination address : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let address ← wordStackLocation config address
  match destination, address with
  | .register destination, .register address =>
      pure (.inst (.mem operator destination address))
  | .stack destination, .register address =>
      pure (.seq (.inst (.mem operator config.scratch address))
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .register destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.inst (.mem operator destination config.addressScratch)))
  | .stack destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.inst (.mem operator config.scratch config.addressScratch))
          (.stackStore config.scratch (wordStackOffset config destination))))

def wordStackStoreInst (config : WordStackConfig) (operator : WordMemOp)
    (source address : Nat) : Option (StackProg α) := do
  let source ← wordStackLocation config source
  let address ← wordStackLocation config address
  match source, address with
  | .register source, .register address =>
      pure (.inst (.mem operator source address))
  | .stack source, .register address =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config source))
        (.inst (.mem operator config.scratch address)))
  | .register source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.inst (.mem operator source config.addressScratch)))
  | .stack source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.stackLoad config.scratch (wordStackOffset config source))
          (.inst (.mem operator config.scratch config.addressScratch))))

def wordStackJoin (first second : StackProg α) : StackProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def wordStackDivInst (config : WordStackConfig)
    (destination dividend divisor : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let dividend ← wordStackLocation config dividend
  let divisor ← wordStackLocation config divisor
  match destination, dividend, divisor with
  | .register destination, .register dividend, .register divisor =>
      pure (.inst (.arith (.div destination dividend divisor)))
  | .register destination, .stack dividend, .register divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (.inst (.arith (.div destination config.scratch divisor))))
  | .register destination, .register dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.addressScratch (wordStackOffset config divisor))
        (.inst (.arith (.div destination dividend config.addressScratch))))
  | .register destination, .stack dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config divisor))
          (.inst (.arith (.div destination config.scratch config.addressScratch)))))
  | .stack destination, .register dividend, .register divisor =>
      pure (wordStackJoin
        (.inst (.arith (.div config.scratch dividend divisor)))
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .stack destination, .stack dividend, .register divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.inst (.arith (.div config.scratch config.scratch divisor)))
          (.stackStore config.scratch (wordStackOffset config destination))))
  | .stack destination, .register dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.addressScratch (wordStackOffset config divisor))
        (wordStackJoin
          (.inst (.arith (.div config.scratch dividend config.addressScratch)))
          (.stackStore config.scratch (wordStackOffset config destination))))
  | .stack destination, .stack dividend, .stack divisor =>
      pure (wordStackJoin
        (.stackLoad config.scratch (wordStackOffset config dividend))
        (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config divisor))
          (wordStackJoin
            (.inst (.arith (.div config.scratch config.scratch config.addressScratch)))
            (.stackStore config.scratch (wordStackOffset config destination)))))

def wordStackArithInst (config : WordStackConfig) : WordArith → Option (StackProg α)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight => do
      let destinationLeft ← wordStackLocation config destinationLeft
      let destinationRight ← wordStackLocation config destinationRight
      let sourceLeft ← wordStackLocation config sourceLeft
      let sourceRight ← wordStackLocation config sourceRight
      match destinationLeft, destinationRight, sourceLeft, sourceRight with
      | .register destinationLeft, .register destinationRight,
          .register sourceLeft, .register sourceRight =>
          pure (.inst (.arith (.longMul destinationLeft destinationRight
            sourceLeft sourceRight)))
      | _, _, _, _ => none
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn => do
      let destination ← wordStackLocation config destination
      let resultCarry ← wordStackLocation config resultCarry
      let sourceLeft ← wordStackLocation config sourceLeft
      let sourceRight ← wordStackLocation config sourceRight
      let carryIn ← wordStackLocation config carryIn
      match destination, resultCarry, sourceLeft, sourceRight, carryIn with
      | .register destination, .register resultCarry, .register sourceLeft,
          .register sourceRight, .register carryIn =>
          pure (.inst (.arith (.addCarry destination resultCarry sourceLeft
            sourceRight carryIn)))
      | _, _, _, _, _ => none
  | .div destination dividend divisor =>
      wordStackDivInst config destination dividend divisor
  | _ => none

def wordStackMemoryInst (config : WordStackConfig) (operator : WordMemOp)
    (sourceOrDestination address : Nat) : Option (StackProg α) :=
  match operator with
  | .load => wordStackLoadInst config operator sourceOrDestination address
  | .load8 => wordStackLoadInst config operator sourceOrDestination address
  | .load16 => wordStackLoadInst config operator sourceOrDestination address
  | .load32 => wordStackLoadInst config operator sourceOrDestination address
  | .store => wordStackStoreInst config operator sourceOrDestination address
  | .store8 => wordStackStoreInst config operator sourceOrDestination address
  | .store16 => wordStackStoreInst config operator sourceOrDestination address
  | .store32 => wordStackStoreInst config operator sourceOrDestination address

def wordStackSharedLoadInst (config : WordStackConfig) (operator : WordMemOp)
    (destination address : Nat) : Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let address ← wordStackLocation config address
  match destination, address with
  | .register destination, .register address =>
      pure (.shMem operator destination address)
  | .stack destination, .register address =>
      pure (.seq (.shMem operator config.scratch address)
        (.stackStore config.scratch (wordStackOffset config destination)))
  | .register destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.shMem operator destination config.addressScratch))
  | .stack destination, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.shMem operator config.scratch config.addressScratch)
          (.stackStore config.scratch (wordStackOffset config destination))))

def wordStackSharedStoreInst (config : WordStackConfig) (operator : WordMemOp)
    (source address : Nat) : Option (StackProg α) := do
  let source ← wordStackLocation config source
  let address ← wordStackLocation config address
  match source, address with
  | .register source, .register address =>
      pure (.shMem operator source address)
  | .stack source, .register address =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config source))
        (.shMem operator config.scratch address))
  | .register source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.shMem operator source config.addressScratch))
  | .stack source, .stack address =>
      pure (.seq (.stackLoad config.addressScratch
          (wordStackOffset config address))
        (.seq (.stackLoad config.scratch (wordStackOffset config source))
          (.shMem operator config.scratch config.addressScratch)))

def wordStackSharedMemoryInst (config : WordStackConfig) (operator : WordMemOp)
    (sourceOrDestination address : Nat) : Option (StackProg α) :=
  match operator with
  | .load => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load8 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load16 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .load32 => wordStackSharedLoadInst config operator sourceOrDestination address
  | .store => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store8 => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store16 => wordStackSharedStoreInst config operator sourceOrDestination address
  | .store32 => wordStackSharedStoreInst config operator sourceOrDestination address

/-! The stack program has explicit control-flow and call carriers.  These
    helpers materialize spilled condition operands and implement the Word
    calling convention's even-numbered result registers.  The labels are
    supplied by the enclosing linker through `WordStackConfig`; keeping them
    in the configuration makes this boundary executable without baking in a
    particular code layout. -/

def wordStackReadRegister (config : WordStackConfig) (name temporary : Nat) :
    Option (StackProg α × Nat) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => pure (.skip, register)
  | .stack slot =>
      pure (.stackLoad temporary (wordStackOffset config slot), temporary)

def wordStackConditionOperands (config : WordStackConfig) (condition : Nat)
    (right : WordRegImm α) :
    Option (StackProg α × Nat × WordRegImm α) := do
  let (conditionPrelude, conditionRegister) ←
    wordStackReadRegister config condition config.scratch
  let (rightPrelude, rightOperand) ← match right with
    | .imm value => pure (.skip, .imm value)
    | .reg name => do
        let (prelude, register) ←
          wordStackReadRegister config name config.addressScratch
        pure (prelude, .reg register)
  pure (wordStackJoin conditionPrelude rightPrelude,
    conditionRegister, rightOperand)

def wordStackStoreName : WordStore α → Option StackStore
  | .temp _ => none
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength

/-! Concrete StackLang words use natural-number constants in this port.  The
    polymorphic Word syntax above is retained for pass composition, while
    these helpers provide the first executable expression compiler for the
    concrete representation.  Atom compilation deliberately uses separate
    value and address scratch registers; callers must keep those registers
    outside the locations assigned to simultaneously live virtual names. -/

def wordStackStoreNameNat : WordStore Nat → Option StackStore
  | .temp address => some (.temp address)
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength

def wordStackAtomNat (config : WordStackConfig) (temporary : Nat) :
    WordExp Nat → Option (StackProg Nat × Nat)
  | .const value => some (.const temporary value, temporary)
  | .var name => wordStackReadRegister config name temporary
  | .lookup store => do
      let store ← wordStackStoreNameNat store
      pure (.get temporary store, temporary)
  | _ => none

def wordStackWritePhysicalNat (config : WordStackConfig) (destination : Nat)
    (body : Nat → StackProg Nat) : Option (StackProg Nat) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register => pure (body register)
  | .stack slot =>
      pure (wordStackJoin (body config.scratch)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackCompileBinaryNat (config : WordStackConfig) (destination : Nat)
    (operator : BinOp) (left right : WordExp Nat) : Option (StackProg Nat) := do
  let (leftPrelude, leftRegister) ←
    wordStackAtomNat config config.scratch left
  let (rightPrelude, rightRegister) ←
    wordStackAtomNat config config.addressScratch right
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .arith operator register leftRegister rightRegister)
  pure (wordStackJoin leftPrelude (wordStackJoin rightPrelude body))

def wordStackCompileShiftNat (config : WordStackConfig) (destination : Nat)
    (operator : Shift) (left right : WordExp Nat) : Option (StackProg Nat) := do
  let (leftPrelude, leftRegister) ←
    wordStackAtomNat config config.scratch left
  let (rightPrelude, rightRegister) ←
    wordStackAtomNat config config.addressScratch right
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .shift operator register leftRegister rightRegister)
  pure (wordStackJoin leftPrelude (wordStackJoin rightPrelude body))

def wordStackCompileLoadNat (config : WordStackConfig) (destination : Nat)
    (address : WordExp Nat) : Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .inst (.mem .load register addressRegister))
  pure (wordStackJoin addressPrelude body)

def wordStackCompileStoreNat (config : WordStackConfig) (address : WordExp Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let (valuePrelude, valueRegister) ←
    wordStackAtomNat config config.scratch value
  pure (wordStackJoin addressPrelude
    (wordStackJoin valuePrelude (.inst (.mem .store valueRegister addressRegister))))

def wordStackCompileSharedNat (config : WordStackConfig)
    (operator : WordMemOp) (destination : Nat) (address : WordExp Nat) :
    Option (StackProg Nat) := do
  let (addressPrelude, addressRegister) ←
    wordStackAtomNat config config.addressScratch address
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .shMem operator register addressRegister)
  pure (wordStackJoin addressPrelude body)

def wordStackCompileExpNat (config : WordStackConfig) (destination : Nat) :
    WordExp Nat → Option (StackProg Nat)
  | .const value =>
      wordStackWritePhysicalNat config destination (.const · value)
  | .var source => wordStackMove config destination source
  | .lookup store => do
      let store ← wordStackStoreNameNat store
      let body ← wordStackWritePhysicalNat config destination
        (.get · store)
      pure body
  | .load address => wordStackCompileLoadNat config destination address
  | .op operator [left, right] =>
      wordStackCompileBinaryNat config destination operator left right
  | .op _ _ => none
  | .shift operator left right =>
      wordStackCompileShiftNat config destination operator left right

def wordStackSetNat (config : WordStackConfig) (store : WordStore Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let store ← wordStackStoreNameNat store
  let (prelude, register) ← wordStackAtomNat config config.scratch value
  pure (wordStackJoin prelude (.set store register))

def wordStackMoveFromPhysical (config : WordStackConfig)
    (destination source : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = source then pure .skip
      else pure (.arith .or register source source)
  | .stack slot =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackMoveToPhysical (config : WordStackConfig)
    (source destination : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))

def wordStackMovesFromPhysical (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | [], _ => some .skip
  | destination :: destinations, source => do
      let first ← wordStackMoveFromPhysical config destination source
      let rest ← wordStackMovesFromPhysical config destinations (source + 2)
      pure (wordStackJoin first rest)
termination_by destinations => sizeOf destinations
decreasing_by all_goals decreasing_trivial

def wordStackMovesToPhysical (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | [], _ => some .skip
  | source :: sources, destination => do
      let first ← wordStackMoveToPhysical config source destination
      let rest ← wordStackMovesToPhysical config sources (destination + 2)
      pure (wordStackJoin first rest)
termination_by sources => sizeOf sources
decreasing_by all_goals decreasing_trivial

def wordStackReturnCode (config : WordStackConfig) :
    Option (List Nat × List Nat) → Option (StackProg α)
  | none => some .skip
  | some (destinations, _) =>
      wordStackMovesFromPhysical config destinations 2

def wordStackReturn (config : WordStackConfig) (values : List Nat) :
    Option (StackProg α) := do
  let moves ← wordStackMovesToPhysical config values 2
  match values with
  | [] => pure moves
  | _ => pure (wordStackJoin moves (.return 2))

def wordToStackInst (config : WordStackConfig) : WordInst → Option (StackProg α)
  | .mem operator sourceOrDestination address =>
      wordStackMemoryInst config operator sourceOrDestination address
  | .arith operation => wordStackArithInst config operation

/-! A compact executable semantics for the move fragment.  StackLang uses
natural-number register names, so this boundary deliberately models the
register file and frame slots independently of the later byte-addressed
RISC-V stack representation. -/
structure WordStackState (width : Nat) where
  registers : Nat → Word width
  stack : Nat → Word width

def wordStackWriteRegister [NeZero width] (state : WordStackState width)
    (register : Nat) (value : Word width) : WordStackState width :=
  { state with registers := fun current =>
      if current = register then value else state.registers current }

def wordStackWriteSlot [NeZero width] (state : WordStackState width)
    (slot : Nat) (value : Word width) : WordStackState width :=
  { state with stack := fun current =>
      if current = slot then value else state.stack current }

def evalWordStackBasic [NeZero width] (state : WordStackState width) :
    StackProg α → Option (WordStackState width)
  | .skip => some state
  | .arith .or destination left right =>
      some (wordStackWriteRegister state destination
        (state.registers left ||| state.registers right))
  | .stackLoad register offset =>
      some (wordStackWriteRegister state register (state.stack offset))
  | .stackStore register offset =>
      some (wordStackWriteSlot state offset (state.registers register))
  | .seq first second => do
      let state ← evalWordStackBasic state first
      evalWordStackBasic state second
  | _ => none

/-! A slightly richer executable StackLang semantics for the concrete Nat
    compiler.  It is intentionally an abstract word-memory model: byte
    layout and RISC-V instruction encoding remain below StackLang, while this
    state is sufficient to state expression-lowering preservation. -/

structure WordStackMachineState (width : Nat) where
  registers : Nat → Word width
  stack : Nat → Word width
  stores : StackStore → Word width
  memory : Word width → Word width
  sharedMemory : Word width → Word width

def wordStackMachineWriteRegister (state : WordStackMachineState width)
    (register : Nat) (value : Word width) : WordStackMachineState width :=
  { state with registers := fun current =>
      if current = register then value else state.registers current }

def wordStackMachineWriteSlot (state : WordStackMachineState width)
    (slot : Nat) (value : Word width) : WordStackMachineState width :=
  { state with stack := fun current =>
      if current = slot then value else state.stack current }

def wordStackMachineWriteStore (state : WordStackMachineState width)
    (store : StackStore) (value : Word width) : WordStackMachineState width :=
  { state with stores := fun current =>
      if current = store then value else state.stores current }

def wordStackMachineWriteMemory (state : WordStackMachineState width)
    (address value : Word width) : WordStackMachineState width :=
  { state with memory := fun current =>
      if current = address then value else state.memory current }

def wordStackMachineWriteSharedMemory (state : WordStackMachineState width)
    (address value : Word width) : WordStackMachineState width :=
  { state with sharedMemory := fun current =>
      if current = address then value else state.sharedMemory current }

def wordStackMachineBinOp : BinOp → Word width → Word width → Word width
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .and, left, right => left &&& right
  | .or, left, right => left ||| right
  | .xor, left, right => left ^^^ right

def wordStackMachineRotateRight (value : Word width) (amount : Word width) :
    Word width :=
  let amount := amount.toNat % width
  BitVec.ushiftRight value amount |||
    BitVec.shiftLeft value ((width - amount) % width)

def wordStackMachineShift : Shift → Word width → Word width → Word width
  | .lsl, left, right => BitVec.shiftLeft left (shiftAmount right)
  | .lsr, left, right => BitVec.ushiftRight left (shiftAmount right)
  | .asr, left, right => BitVec.sshiftRight left (shiftAmount right)
  | .ror, left, right => wordStackMachineRotateRight left right

def evalWordStackMachine [NeZero width]
    (state : WordStackMachineState width) :
    StackProg Nat → Option (WordStackMachineState width)
  | .skip => some state
  | .const destination value =>
      some (wordStackMachineWriteRegister state destination
        (BitVec.ofNat width value))
  | .arith operator destination left right =>
      some (wordStackMachineWriteRegister state destination
        (wordStackMachineBinOp operator
          (state.registers left) (state.registers right)))
  | .shift operator destination left right =>
      some (wordStackMachineWriteRegister state destination
        (wordStackMachineShift operator
          (state.registers left) (state.registers right)))
  | .inst (.mem .load destination address) =>
      some (wordStackMachineWriteRegister state destination
        (state.memory (state.registers address)))
  | .inst (.mem .store source address) =>
      some (wordStackMachineWriteMemory state
        (state.registers address) (state.registers source))
  | .shMem .load destination address =>
      some (wordStackMachineWriteRegister state destination
        (state.sharedMemory (state.registers address)))
  | .shMem .store source address =>
      some (wordStackMachineWriteSharedMemory state
        (state.registers address) (state.registers source))
  | .get destination store =>
      some (wordStackMachineWriteRegister state destination (state.stores store))
  | .set store source =>
      some (wordStackMachineWriteStore state store (state.registers source))
  | .stackLoad register offset =>
      some (wordStackMachineWriteRegister state register (state.stack offset))
  | .stackStore register offset =>
      some (wordStackMachineWriteSlot state offset (state.registers register))
  | .seq first second => do
      let state ← evalWordStackMachine state first
      evalWordStackMachine state second
  | _ => none

def wordStackMachineValue [NeZero width] (config : WordStackConfig)
    (state : WordStackMachineState width) (name : Nat) : Option (Word width) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => some (state.registers register)
  | .stack slot => some (state.stack (wordStackOffset config slot))

theorem evalWordStackMachine_const_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination value : Nat) (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (heval : (wordStackCompileExpNat config destination (.const value)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (BitVec.ofNat width value) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  simp [wordStackCompileExpNat, wordStackWritePhysicalNat, hdestination] at heval
  cases destinationLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      hdestination] at heval ⊢
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, hdestination]

def wordStackValue [NeZero width] (config : WordStackConfig)
    (state : WordStackState width) (name : Nat) : Option (Word width) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => some (state.registers register)
  | .stack slot => some (state.stack (wordStackOffset config slot))

theorem evalWordStackBasic_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackState width)
    (destination source : Nat) (destinationLocation sourceLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination_scratch : destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackBasic state) = some final) :
      wordStackValue config final destination =
      wordStackValue config state source := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  simp [wordStackMove, hdestination, hsource] at heval
  cases destinationLocation <;> cases sourceLocation <;>
    simp [evalWordStackBasic, wordStackValue, wordStackLocation,
      wordStackOffset, wordStackWriteRegister, wordStackWriteSlot,
      hdestination, hsource, hdestination_scratch, hsource_scratch] at heval ⊢
  all_goals
    cases heval
    simp [wordStackValue, wordStackLocation, wordStackOffset,
      wordStackWriteRegister, wordStackWriteSlot,
      hdestination, hsource, hdestination_scratch, hsource_scratch]

def wordToStackProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α] [DecidableRel (fun left right : α => left < right)]
    (config : WordStackConfig) : WordProg α → Option (StackProg α)
  | .skip => some .skip
  | .assign destination (.var source) =>
      wordStackMove config destination source
  | .locValue destination source =>
      wordStackMove config destination source
  | .inst instruction =>
      wordToStackInst config instruction
  | .store (.var address) value =>
      wordStackMemoryInst config .store value address
  | .set store (.var source) => do
      let store ← wordStackStoreName store
      let (prelude, register) ←
        wordStackReadRegister config source config.scratch
      pure (wordStackJoin prelude (.set store register))
  | .seq first second => do
      let first ← wordToStackProg config first
      let second ← wordToStackProg config second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let thenBranch ← wordToStackProg config thenBranch
      let elseBranch ← wordToStackProg config elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch))
  | .loop _ body _ => do
      let body ← wordToStackProg config body
      pure (.loop body)
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return _ values => wordStackReturn config values
  | .tick => pure .tick
  | .call returns (some target) arguments none => do
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      pure (wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        config.returnLabel config.entryLabel)
  | .call returns (some target) arguments (some (exception, body)) => do
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let handlerCode ← wordToStackProg config body
      pure (wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception)
  | .ffi function configuration configurationLength array arrayLength _ =>
      pure (wordToStackFfi function configuration configurationLength array arrayLength)
  | .shareInst operator name (.var address) =>
      wordStackSharedMemoryInst config operator name address
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! Concrete program compiler.  This specializes only the value representation
    (constants and temporary store names) to `Nat`; the generic compiler above
    remains available for syntax-only clients. -/

def wordToStackProgNat [BEq Nat] (config : WordStackConfig) :
    WordProg Nat → Option (StackProg Nat)
  | .skip => some .skip
  | .assign destination value => wordStackCompileExpNat config destination value
  | .locValue destination source => wordStackMove config destination source
  | .inst instruction => wordToStackInst config instruction
  | .store address value =>
      wordStackCompileStoreNat config address (.var value)
  | .set store value => wordStackSetNat config store value
  | .seq first second => do
      let first ← wordToStackProgNat config first
      let second ← wordToStackProgNat config second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let thenBranch ← wordToStackProgNat config thenBranch
      let elseBranch ← wordToStackProgNat config elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch))
  | .loop _ body _ => do
      let body ← wordToStackProgNat config body
      pure (.loop body)
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return _ values => wordStackReturn config values
  | .tick => pure .tick
  | .call returns (some target) arguments none => do
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      pure (wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        config.returnLabel config.entryLabel)
  | .call returns (some target) arguments (some (exception, body)) => do
      let returnCode ← wordStackReturnCode config returns
      let handlerCode ← wordToStackProgNat config body
      pure (wordToStackCallWithHandler config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel config.handlerLabel exception)
  | .call _ none _ _ => none
  | .ffi function configuration configurationLength array arrayLength _ =>
      pure (wordToStackFfi function configuration configurationLength array arrayLength)
  | .shareInst operator name address =>
      wordStackCompileSharedNat config operator name address
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! The real Word pipeline is indexed by a fixed-width bit-vector type, while
    StackProg keeps constants as natural numbers so that StackRemove can
    materialize them at the target width.  This adapter makes that boundary
    explicit: converting a Word constant to `toNat` is recovered by the
    subsequent `BitVec.ofNat` performed by the StackLang machine and LabLang
    backend. -/

def wordStoreToNat : WordStore (Word width) → WordStore Nat
  | .temp address => .temp address.toNat
  | .currHeap => .currHeap
  | .heapLength => .heapLength

def wordExpToNat : WordExp (Word width) → WordExp Nat
  | .const value => .const value.toNat
  | .var name => .var name
  | .lookup store => .lookup (wordStoreToNat store)
  | .load address => .load (wordExpToNat address)
  | .op operator arguments => .op operator (arguments.map wordExpToNat)
  | .shift operator left right =>
      .shift operator (wordExpToNat left) (wordExpToNat right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordRegImmToNat : WordRegImm (Word width) → WordRegImm Nat
  | .imm value => .imm value.toNat
  | .reg name => .reg name

def wordProgToNat : WordProg (Word width) → WordProg Nat
  | .skip => .skip
  | .assign name value => .assign name (wordExpToNat value)
  | .inst instruction => .inst instruction
  | .store address value => .store (wordExpToNat address) value
  | .set store value => .set (wordStoreToNat store) (wordExpToNat value)
  | .seq first second => .seq (wordProgToNat first) (wordProgToNat second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition (wordRegImmToNat right)
        (wordProgToNat thenBranch) (wordProgToNat elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordProgToNat body) liveOut
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return label values => .return label values
  | .tick => .tick
  | .locValue destination source => .locValue destination source
  | .call returns target arguments none =>
      .call (returns.map (fun (values, live) => (values, live))) target
        arguments none
  | .call returns target arguments (some (exception, body)) =>
      .call (returns.map (fun (values, live) => (values, live))) target
        arguments (some (exception, wordProgToNat body))
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function configuration configurationLength array arrayLength live
  | .shareInst operator name address =>
      .shareInst operator name (wordExpToNat address)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordToStackProgWord [NeZero width] (config : WordStackConfig)
    (program : WordProg (Word width)) : Option (StackProg Nat) :=
  wordToStackProgNat config (wordProgToNat program)

/-! Location map used by the currently register-coloured pipeline fragment.
    It is intentionally identity-based; the spill-aware allocator will
    replace this with a map containing `WordLocation.stack` entries once its
    StackLang frame contract is connected. -/
def wordStackIdentityConfig [NeZero width]
    (program : WordProg (Word width)) : WordStackConfig :=
  { locations := (wordProgVariables program).eraseDups.map
      (fun name => (name, .register name))
    scratch := 31
    stackBase := 0
    addressScratch := 29 }

theorem wordStackMove_registers :
    wordStackMove
        { locations := [(0, .register 4), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.arith .or 4 5 5 : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, lookupNatInfo]

theorem wordStackMove_register_to_spill :
    wordStackMove
        { locations := [(0, .stack 2), (1, .register 5)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.arith .or 31 5 5) (.stackStore 31 12) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMove_spill_to_register :
    wordStackMove
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.stackLoad 31 12) (.arith .or 4 31 31) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMove_spill_to_spill :
    wordStackMove
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.seq (.stackLoad 31 12) (.stackStore 31 13) : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMemoryInst_load_spill_address :
    wordStackMemoryInst
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .load32 0 1 =
      some (.seq (.stackLoad 29 12) (.inst (.mem .load32 4 29)) : StackProg Nat) := by
  simp [wordStackMemoryInst, wordStackLoadInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

theorem wordStackMemoryInst_store_spill_value_and_address :
    wordStackMemoryInst
        { locations := [(0, .stack 3), (1, .stack 2)],
          scratch := 31, stackBase := 10 } .store32 0 1 =
      some (.seq (.stackLoad 29 12)
        (.seq (.stackLoad 31 13) (.inst (.mem .store32 31 29))) : StackProg Nat) := by
  simp [wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

theorem wordStackDivInst_spill_operands :
    wordStackDivInst
        { locations := [(0, .stack 3), (1, .stack 2), (2, .register 6)],
          scratch := 31, stackBase := 10 } 0 1 2 =
      some (.seq (.stackLoad 31 12)
        (.seq (.inst (.arith (.div 31 31 6)))
          (.stackStore 31 13)) : StackProg Nat) := by
  simp [wordStackDivInst, wordStackJoin, wordStackLocation,
    wordStackOffset, lookupNatInfo]




end Flapjack.RiscV
