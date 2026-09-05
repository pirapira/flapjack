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
