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

def wordToStackInst (config : WordStackConfig) : WordInst → Option (StackProg α)
  | .mem operator sourceOrDestination address =>
      wordStackMemoryInst config operator sourceOrDestination address
  | .arith _ => none

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
  | .seq first second => do
      let first ← wordToStackProg config first
      let second ← wordToStackProg config second
      pure (.seq first second)
  | _ => none
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

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

end Flapjack.RiscV
