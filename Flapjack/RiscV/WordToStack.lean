import Flapjack.Stack
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.RegAlloc

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
  specialScratch : Nat := 28
  carryScratch : Nat := 27
  perf : Bool := false
  frameOffset : Nat := 0
  returnLabel : Nat := 0
  entryLabel : Nat := 0
  sectionId : Nat := 0
  handlerLabel : Nat := 0
  /- Physical register used for the first word-level argument/result slot.
     Ordinary RISC-V pipeline configurations use hardware `x10`; the
     source-shaped Cake LongDiv helper retains its original stack ABI base. -/
  abiBase : Nat := 1
  /- Physical ABI argument/result registers are consecutive on RISC-V.  The
     source-shaped Cake helper retains its historical two-slot numbering. -/
  abiStride : Nat := 2
  /- Source-shaped Cake calls include the link slot (Word name 0) in their
     argument list, while value returns still begin at abiBase. -/
  callAbiBase : Nat := 1
  /- Number of physical ABI argument/result slots.  Cake's RISC-V window is
     x10--x21; values after this window use the current Cake frame. -/
  abiRegisterCount : Nat := 12
  /- Cake's `f` frame size used by `format_var`/`wMoveSingle`.  The public
     pipeline records `stack_var_count` (`f'`), so this is normally `f'+1`
     when the frame is non-empty. -/
  abiFrameSlots : Nat := 0
  deriving Repr

/-! The executable StackLang model carries hardware RISC-V register numbers
    directly at the ABI boundary.  The CakeML ABI's first argument/result
    register is stack register 1, which is hardware `x10`; the existing `+2`
    layout supplies subsequent word locations. -/
def wordStackAbiBase : Nat := 10

def wordStackLocation (config : WordStackConfig) (name : Nat) :
    Option WordLocation :=
  lookupNatInfo name config.locations

def wordStackOffset (config : WordStackConfig) (slot : Nat) : Nat :=
  config.stackBase + slot

/-! Cake's `compile_prog` chooses `f = 0` for an empty frame and otherwise
    `f = stack_var_count + 1`.  Keep the conversion at the ABI boundary so
    callers can continue to provide the source-shaped `f'` occupancy. -/
def wordStackCakeFrameSize (config : WordStackConfig) : Nat :=
  if config.abiFrameSlots = 0 then 0 else config.abiFrameSlots + 1

/-! `format_var k` classifies the first `k` physical argument slots as
    registers and the remaining slots as frame variables.  `wMoveSingle`
    materializes a frame variable at `f - 1 - (r - k)`; this is the direct
    location form used by the parallel move compiler below. -/
def wordStackPhysicalLocation (config : WordStackConfig)
    (index base : Nat) : WordLocation :=
  if index < config.abiRegisterCount then
    .register (base + config.abiStride * index)
  else
    .stack (wordStackCakeFrameSize config - 1 -
      (index - config.abiRegisterCount))

def wordStackMove {α : Type} (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) := do
  let destination ← wordStackLocation config destination
  let source ← wordStackLocation config source
  match destination, source with
  | .register destination, .register source =>
      if destination = source then pure .skip
      else pure (.arith .or destination source source)
  | .register destination, .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))
  | .stack slot, .register source =>
      pure (.stackStore source (wordStackOffset config slot))
  | .stack destinationSlot, .stack sourceSlot =>
      if destinationSlot = sourceSlot then pure .skip
      else pure (.seq (.stackLoad config.scratch
            (wordStackOffset config sourceSlot))
          (.stackStore config.scratch (wordStackOffset config destinationSlot)))

/-! A `LocValue` materializes a code label, rather than reading a source
    variable.  A register destination can receive the StackLang instruction
    directly; a spilled destination is materialized in the reserved scratch
    register and then stored in its stack slot.  The entry field is zero for
    the ordinary code-label values emitted by CakeML's Word-to-Stack pass. -/
def wordStackLocValue {α : Type} (config : WordStackConfig) (destination label : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      pure (.locValue register label 0)
  | .stack slot =>
      pure (.seq (.locValue config.scratch label 0)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordToStackMove {α : Type} (config : WordStackConfig) (destination source : Nat) :
    Option (StackProg α) :=
  wordStackMove config destination source

def wordStackLoadInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackStoreInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackJoin {α : Type} (first second : StackProg α) : StackProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def wordMoveDestinations (moves : List (Nat × Nat)) : List Nat :=
  moves.map (fun move => move.1)

def wordMoveRemoveDestination (destination : Nat) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.filter (fun move => move.1 != destination)

def wordMoveReady (destinations : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | move :: moves =>
      if move.1 ∉ destinations then
        some move
      else
        wordMoveReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordStackMoveToScratch {α : Type} (config : WordStackConfig) (source : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or config.addressScratch register register)
  | .stack slot =>
      pure (.stackLoad config.addressScratch (wordStackOffset config slot))

def wordStackMoveFromScratch {α : Type} (config : WordStackConfig) (destination : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or register config.addressScratch config.addressScratch)
  | .stack slot =>
      pure (.stackStore config.addressScratch (wordStackOffset config slot))

/-! Compile a parallel move list.  A move whose source is not another pending
    destination reads a value that no remaining move overwrites, so it is safe
    to emit **last**; emitting it first would clobber a destination that an
    earlier-listed move still has to read (e.g. `[a <- b, b <- c]` must emit
    `a <- b` before `b <- c`).  This is the same scheduling the original
    allocator's `parmove` performs (`compiler/backend/reg_alloc/parmoveScript.sml`).
    If the remaining graph is a cycle, save one source in the reserved scratch
    register, solve the rest, and restore that saved value into the postponed
    destination.  CakeML's `parmove` uses the same temporary-register idea; the
    explicit `Nodup` check is its windmill invariant at this boundary.
    Stack-to-stack moves use `scratch`, so cycle save/restore uses the
    independent address scratch.  The allocator reserves both registers for
    this purpose. -/
def wordStackParallelMoveAux {α : Type} (config : WordStackConfig) :
    Nat → List (Nat × Nat) → Option (StackProg α)
  | 0, _ => none
  | fuel + 1, moves =>
      let destinations := wordMoveDestinations moves
      let sources := moves.map (fun move => move.2)
      if !destinations.Nodup then
        none
      else if moves.isEmpty then
        some .skip
      else
        match wordMoveReady sources moves with
        | some (destination, source) => do
            let first ← wordStackMove config destination source
            let rest ← wordStackParallelMoveAux config fuel
              (wordMoveRemoveDestination destination moves)
            pure (wordStackJoin first rest)
        | none =>
            match moves with
            | [] => some .skip
            | (destination, source) :: _ => do
                let save ← wordStackMoveToScratch config source
                let rest ← wordStackParallelMoveAux config fuel
                  (wordMoveRemoveDestination destination moves)
                let restore ← wordStackMoveFromScratch config destination
                pure (wordStackJoin save (wordStackJoin rest restore))

def wordStackParallelMove {α : Type} (config : WordStackConfig)
    (moves : List (Nat × Nat)) : Option (StackProg α) :=
  let moves := moves.filter (fun move => move.1 != move.2)
  wordStackParallelMoveAux config (moves.length + 1) moves

def wordStackMoveList {α : Type} (config : WordStackConfig) :
    List (Nat × Nat) → Option (StackProg α) :=
  wordStackParallelMove config

def wordStackDivInst {α : Type} (config : WordStackConfig)
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

/-! Cake's `word_to_stack` never rejects an operand colour: spilled
    operands stage through the two registers just past the colour range
    (`wReg1`/`wReg2`, `word_to_stackScript.sml:28-56`) and those registers
    are never coloured, so no exclusion check is needed at all.  The
    residual check below only guards against a mis-configured pipeline that
    would allocate variables onto the two staging registers. -/
def wordStackLongMulLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch
  | .stack _ => true

def wordStackAddCarryLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch
  | .stack _ => true

def wordStackLongMulLocationsSafe {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Bool :=
  match operation with
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      match wordStackLocation config destinationLeft,
        wordStackLocation config destinationRight,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight with
      | some destinationLeft, some destinationRight,
          some sourceLeft, some sourceRight =>
          wordStackLongMulLocationSafe config destinationLeft &&
            wordStackLongMulLocationSafe config destinationRight &&
            wordStackLongMulLocationSafe config sourceLeft &&
            wordStackLongMulLocationSafe config sourceRight
      | _, _, _, _ => false
  | _ => false

def wordStackLongMulMoveToPhysical {α : Type} (config : WordStackConfig)
    (source destination : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))

def wordStackLongMulMoveFromPhysical {α : Type} (config : WordStackConfig)
    (destination source : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = source then pure .skip
      else pure (.arith .or register source source)
  | .stack slot =>
      pure (.stackStore source (wordStackOffset config slot))

def wordStackLongMulInst {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Option (StackProg α) :=
  match operation with
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      /- As for `AddCarry`, CakeML's `wInst` emits the architectural
         instruction directly when the operands already live in registers and
         only loads them through the frame otherwise
         (`word_to_stackScript.sml` via `wReg1`, `wReg2`, `wRegWrite1`), so the
         scratch-exclusion guard only restricts the loading fallback. -/
      match wordStackLocation config destinationLeft,
        wordStackLocation config destinationRight,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight with
      | some (.register destinationLeft), some (.register destinationRight),
          some (.register sourceLeft), some (.register sourceRight) =>
          pure (.inst (.arith (.longMul destinationLeft destinationRight
            sourceLeft sourceRight)))
      | _, _, _, _ =>
        match wordStackLocation config destinationLeft,
          wordStackLocation config destinationRight,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight with
        | some destLeftLocation, some destRightLocation,
            some leftLocation, some rightLocation =>
            /- Cake's `wInst` staging discipline (`word_to_stackScript.sml:28-56`):
               a spilled source loads through the first register past the
               colour range (`wReg1`, here `config.scratch`), a second spilled
               source through the next one (`wReg2`, here
               `config.addressScratch`), and a spilled destination is written
               by letting the instruction overwrite that same register after
               the reads (`wRegWrite1`), so no operand colour is ever rejected
               and no load-order juggling is required. -/
            let dLReg := match destLeftLocation with
              | .register register => register
              | _ => config.scratch
            let dRReg := match destRightLocation with
              | .register register => register
              | _ => config.addressScratch
            let sLReg := match leftLocation with
              | .register register => register
              | _ => config.scratch
            let sRReg := match rightLocation with
              | .register register => register
              | _ => config.addressScratch
            do
              let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
                sLReg
              let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
                sRReg
              let writeLeft ← wordStackLongMulMoveFromPhysical config
                destinationLeft dLReg
              let writeRight ← wordStackLongMulMoveFromPhysical config
                destinationRight dRReg
              pure (wordStackJoin loadLeft
                (wordStackJoin loadRight
                  (wordStackJoin
                    (.inst (.arith (.longMul dLReg dRReg sLReg sRReg)))
                    (wordStackJoin writeLeft writeRight))))
        | _, _, _, _ => none
  | _ => none

def wordStackAddCarryInst {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Option (StackProg α) :=
  match operation with
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      /- CakeML's `wInst (Arith (AddCarry n1 n2 n3 n4))` emits the
         architectural instruction directly whenever the operands already
         live in registers, and only falls back to loading them through the
         frame otherwise (`word_to_stackScript.sml:114-118` via `wReg1`,
         `wReg2` and `wRegWrite1`).  The all-register case therefore does not
         touch any scratch register, so the scratch-exclusion guard below
         must only restrict the fallback: guarding the direct case made the
         lowering fail whenever the allocator coloured an operand with a
         scratch register such as the carry scratch (GH #1015 `u256_sub`). -/
      match wordStackLocation config destination,
        wordStackLocation config resultCarry,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight,
        wordStackLocation config carryIn with
      | some (.register destination), some (.register resultCarry),
          some (.register sourceLeft), some (.register sourceRight),
          some (.register carryIn) =>
          some (.inst (.arith (.addCarry destination resultCarry sourceLeft
            sourceRight carryIn)))
      | _, _, _, _, _ =>
        match wordStackLocation config destination,
          wordStackLocation config resultCarry,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight,
          wordStackLocation config carryIn with
        | some destLocation, some rcLocation, some leftLocation,
            some rightLocation, some carryLocation =>
            /- Cake's staging discipline (`word_to_stackScript.sml:28-56`,
               `:114-118`): spilled sources load through the two registers
               just past the colour range, spilled destinations are written by
               overwriting those registers after the reads, and the carry
               input `n4` is passed straight through without staging.  A
               register may be read as a source and then written as a
               destination in the same instruction (`wRegWrite1`), so no
               operand colour is ever rejected. -/
            let dReg := match destLocation with
              | .register register => register
              | _ => config.scratch
            let rcReg := match rcLocation with
              | .register register => register
              | _ => config.addressScratch
            let sLReg := match leftLocation with
              | .register register => register
              | _ => config.scratch
            let sRReg := match rightLocation with
              | .register register => register
              | _ => config.addressScratch
            -- A spilled carry input borrows a staging register that no
            -- other spilled source already occupies; with three spilled
            -- sources there is none left, and the lowering fails
            -- explicitly (Cake never stages `n4`, so it never faces this).
            match carryLocation with
            | .register carryIn =>
                do
                  let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
                    sLReg
                  let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
                    sRReg
                  let writeDestination ← wordStackLongMulMoveFromPhysical config
                    destination dReg
                  let writeResultCarry ← wordStackLongMulMoveFromPhysical config
                    resultCarry rcReg
                  pure (wordStackJoin loadLeft
                    (wordStackJoin loadRight
                      (wordStackJoin
                        (.inst (.arith (.addCarry dReg rcReg sLReg sRReg
                          carryIn)))
                        (wordStackJoin writeDestination writeResultCarry))))
            | _ =>
                let carryReg :=
                  if sLReg != config.scratch then config.scratch
                  else if sRReg != config.addressScratch then config.addressScratch
                  else config.scratch
                if carryLocation == .register carryReg || (sLReg == config.scratch &&
                    sRReg == config.addressScratch) then none
                else
                  do
                    let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
                      sLReg
                    let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
                      sRReg
                    let loadCarry ← wordStackLongMulMoveToPhysical config carryIn
                      carryReg
                    let writeDestination ← wordStackLongMulMoveFromPhysical config
                      destination dReg
                    let writeResultCarry ← wordStackLongMulMoveFromPhysical config
                      resultCarry rcReg
                    pure (wordStackJoin loadLeft
                      (wordStackJoin loadRight
                        (wordStackJoin loadCarry
                          (wordStackJoin
                            (.inst (.arith (.addCarry dReg rcReg sLReg sRReg
                              carryReg)))
                            (wordStackJoin writeDestination writeResultCarry)))))
        | _, _, _, _, _ => none
  | _ => none

/-! Lower CakeML WordLang's four-register AddCarry without re-encoding it as
    Pancake's five-register two-result operation.  The fourth register is
    deliberately both the carry input and carry output. -/
def wordStackCakeAddCarryInst {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Option (StackProg α) :=
  match operation with
  | .cakeAddCarry destination sourceLeft sourceRight carry =>
      /- The all-register case emits the architectural instruction directly and
         needs no scratch register, so the guard only restricts the fallback
         (see `wordStackAddCarryInst`). -/
      match wordStackLocation config destination,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight,
        wordStackLocation config carry with
      | some (.register destination), some (.register sourceLeft),
          some (.register sourceRight), some (.register carry) =>
          some (.inst (.arith (.cakeAddCarry destination sourceLeft
            sourceRight carry)))
      | _, _, _, _ =>
        match wordStackLocation config destination,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight,
          wordStackLocation config carry with
        | some destLocation, some leftLocation, some rightLocation,
            some carryLocation =>
            /- Same `wReg1`/`wReg2`/`wRegWrite1` discipline as `AddCarry`
               (`word_to_stackScript.sml:114-118`): the fourth register is
               both carry input and output and is passed straight through
               whenever it lives in a register.  A spilled carry stages into
               a staging register that neither spilled source occupies and
               that differs from the destination register (the instruction
               writes both); when none is left the lowering fails
               explicitly, matching Cake which never stages `n4`. -/
            let dReg := match destLocation with
              | .register register => register
              | _ => config.scratch
            let sLReg := match leftLocation with
              | .register register => register
              | _ => config.scratch
            let sRReg := match rightLocation with
              | .register register => register
              | _ => config.addressScratch
            match carryLocation with
            | .register carryRegister =>
                do
                  let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
                    sLReg
                  let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
                    sRReg
                  let writeDestination ← wordStackLongMulMoveFromPhysical config
                    destination dReg
                  let writeCarry ← wordStackLongMulMoveFromPhysical config carry
                    carryRegister
                  pure (wordStackJoin loadLeft
                    (wordStackJoin loadRight
                      (wordStackJoin
                        (.inst (.arith (.cakeAddCarry dReg sLReg sRReg
                          carryRegister)))
                        (wordStackJoin writeDestination writeCarry))))
            | _ =>
                let carryReg :=
                  if sLReg != config.scratch && dReg != config.scratch then
                    config.scratch
                  else if sLReg != config.addressScratch &&
                      dReg != config.addressScratch then
                    config.addressScratch
                  else config.scratch
                if dReg == carryReg || sLReg == carryReg || sRReg == carryReg then
                  none
                else
                  do
                    let loadLeft ← wordStackLongMulMoveToPhysical config sourceLeft
                      sLReg
                    let loadRight ← wordStackLongMulMoveToPhysical config sourceRight
                      sRReg
                    let loadCarry ← wordStackLongMulMoveToPhysical config carry
                      carryReg
                    let writeDestination ← wordStackLongMulMoveFromPhysical config
                      destination dReg
                    let writeCarry ← wordStackLongMulMoveFromPhysical config carry
                      carryReg
                    pure (wordStackJoin loadLeft
                      (wordStackJoin loadRight
                        (wordStackJoin loadCarry
                          (wordStackJoin
                            (.inst (.arith (.cakeAddCarry dReg sLReg sRReg
                              carryReg)))
                            (wordStackJoin writeDestination writeCarry)))))
        | _, _, _, _ => none
  | _ => none

/-! CakeML's `LongDiv` uses a fixed four-register convention: the two-word
    dividend is in x3:x0, the quotient is written to x0, and the remainder to
    x3.  The source operation's first four register fields are metadata for
    this convention; only the divisor operand remains allocator-dependent.
    Match CakeML's `wInst` by accepting those fields and normalizing the
    emitted StackLang operation to `LongDiv 0 3 3 0 divisor`. -/
def wordStackLongDivInst {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Option (StackProg α) :=
  match operation with
  | .longDiv _ _ _ _ divisor => do
      let location ← wordStackLocation config divisor
      match location with
      | .register divisorRegister =>
          if divisorRegister = 0 || divisorRegister = 3 then
            none
          else
            pure (.inst (.arith (.longDiv 0 3 3 0 divisorRegister)))
      | .stack slot =>
          pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
            (.inst (.arith (.longDiv 0 3 3 0 config.scratch))))
  | _ => none

/-- `LongMul` may write its high and low words to the same location when only
    the low product is observed, exactly as the compiler emits for `a * b`.
    The shared special-location contract rejects that alias; this relaxed
    contract keeps the source-distinctness requirement so the high product
    cannot clobber an operand before the low product is formed. -/
def wordStackLongMulAliasLocationsSafe {α : Type} (config : WordStackConfig)
    (operation : WordArith α) : Bool :=
  match operation with
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      match wordStackLocation config destinationLeft,
        wordStackLocation config destinationRight,
        wordStackLocation config sourceLeft,
        wordStackLocation config sourceRight with
      | some destinationLeft, some destinationRight,
          some sourceLeft, some sourceRight =>
          destinationLeft = destinationRight &&
            destinationLeft != sourceLeft && destinationLeft != sourceRight
      | _, _, _, _ => false
  | _ => false

def wordStackArithInst {α : Type} (config : WordStackConfig) (operation : WordArith α) :
    Option (StackProg α) :=
  if wordSpecialArithLocationsSafe operation config.locations = true then
    match operation with
    | .longMul _ _ _ _ =>
      wordStackLongMulInst config operation
    | .addCarry _ _ _ _ _ =>
      wordStackAddCarryInst config operation
    | .cakeAddCarry _ _ _ _ =>
      wordStackCakeAddCarryInst config operation
    | .div destination dividend divisor =>
      wordStackDivInst config destination dividend divisor
    | .longDiv _ _ _ _ _ => wordStackLongDivInst config operation
    | .binOp operator destination sourceLeft (.reg sourceRight) =>
      /- Cake's `inst_select` emits a binary operation whose operands are
         register numbers, so the StackLang form is the direct
         register-operand arithmetic instruction whenever all three word
         locations are already registers. -/
      match wordStackLocation config destination,
          wordStackLocation config sourceLeft,
          wordStackLocation config sourceRight with
      | some (.register destination), some (.register sourceLeft),
          some (.register sourceRight) =>
        some (.arith operator destination sourceLeft sourceRight)
      | _, _, _ => none
    | .binOp _ _ _ (.imm _) => none
    | .shift _ _ _ (.reg _) => none
    | .shift _ _ _ (.imm _) => none
  else if wordStackLongMulAliasLocationsSafe config operation then
    wordStackLongMulInst config operation
  else
    none

def wordStackMemoryInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackStoreLocationsSafe (config : WordStackConfig) :
    WordLocation → WordLocation → Bool
  | .register _, .register _ => true
  | .stack _, .register address => address != config.scratch
  | .register source, .stack _ => source != config.addressScratch
  | .stack _, .stack _ => config.scratch != config.addressScratch

def wordStackDivLocationSafe (config : WordStackConfig) :
    WordLocation → Bool
  | .register register =>
      register != config.scratch && register != config.addressScratch
  | .stack _ => true

def wordStackSharedLoadInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackSharedStoreInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackSharedMemoryInst {α : Type} (config : WordStackConfig) (operator : WordMemOp)
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

def wordStackReadRegister {α : Type} (config : WordStackConfig) (name temporary : Nat) :
    Option (StackProg α × Nat) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => pure (.skip, register)
  | .stack slot =>
      pure (.stackLoad temporary (wordStackOffset config slot), temporary)

def wordStackConditionOperands {α : Type} (config : WordStackConfig) (condition : Nat)
    (right : WordRegImm α) :
    Option (StackProg α × Nat × WordRegImm α) := do
  let conditionTemporary :=
    match right with
    | .imm _ => config.addressScratch
    | .reg _ => config.scratch
  let (conditionPrelude, conditionRegister) ←
    wordStackReadRegister config condition conditionTemporary
  let (rightPrelude, rightOperand) ← match right with
    | .imm value => pure (.skip, .imm value)
    | .reg name => do
        let (prelude, register) ←
          wordStackReadRegister config name config.addressScratch
        pure (prelude, .reg register)
  pure (wordStackJoin conditionPrelude rightPrelude,
    conditionRegister, rightOperand)

/-! The ordinary StackLang path names FFI arguments by hardware registers
    x10--x13.  The source-shaped runtime adapter normalizes its exact
    pre-Lab ABI-copy suffix separately, so this general lowering remains the
    hardware-numbered implementation used by its existing contracts. -/

def wordStackFfiRegisterSafe (register : Nat) : Bool :=
  register != 10 && register != 11 && register != 12 && register != 13

def wordStackFfiSourceSafe (config : WordStackConfig) (name : Nat) : Bool :=
  match wordStackLocation config name with
  | some (.register register) => wordStackFfiRegisterSafe register
  | some (.stack _) => true
  | none => false

def wordStackFfiSourcesSafe (config : WordStackConfig) : List Nat → Bool
  | [] => true
  | name :: names =>
      wordStackFfiSourceSafe config name && wordStackFfiSourcesSafe config names

def wordStackFfiMove {α : Type} (config : WordStackConfig) (source destination : Nat) :
    Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))

def wordStackStoreName : WordStore α → Option StackStore
  | .temp _ => none
  | .nextFree => some .nextFree
  | .endOfHeap => some .endOfHeap
  | .triggerGC => some .triggerGC
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength
  | .progStart => some .progStart
  | .bitmapBase => some .bitmapBase
  | .otherHeap => some .otherHeap
  | .allocSize => some .allocSize
  | .globals => some .globals
  | .globReal => some .globReal
  | .handler => some .handler
  | .genStart => some .genStart
  | .codeBuffer => some .codeBuffer
  | .codeBufferEnd => some .codeBufferEnd
  | .bitmapBuffer => some .bitmapBuffer
  | .bitmapBufferEnd => some .bitmapBufferEnd

/-! Concrete StackLang words use natural-number constants in this port.  The
    polymorphic Word syntax above is retained for pass composition, while
    these helpers provide the first executable expression compiler for the
    concrete representation.  Atom compilation deliberately uses separate
    value and address scratch registers; callers must keep those registers
    outside the locations assigned to simultaneously live virtual names. -/

def wordStackStoreNameNat : WordStore Nat → Option StackStore
  | .temp address => some (.temp address)
  | .nextFree => some .nextFree
  | .endOfHeap => some .endOfHeap
  | .triggerGC => some .triggerGC
  | .currHeap => some .currHeap
  | .heapLength => some .heapLength
  | .progStart => some .progStart
  | .bitmapBase => some .bitmapBase
  | .otherHeap => some .otherHeap
  | .allocSize => some .allocSize
  | .globals => some .globals
  | .globReal => some .globReal
  | .handler => some .handler
  | .genStart => some .genStart
  | .codeBuffer => some .codeBuffer
  | .codeBufferEnd => some .codeBufferEnd
  | .bitmapBuffer => some .bitmapBuffer
  | .bitmapBufferEnd => some .bitmapBufferEnd

/-! Bitmap accumulation used by CakeML's `word_to_stack` pass.

    CakeML stores bitmaps as a flat append-only word list.  The first word of
    each bitmap chunk records which following constant words are pointers;
    liveness bitmaps have one additional terminating pointer bit.  Keeping
    the accumulator explicit makes the state change caused by `Alloc` and
    `StoreConsts` observable, rather than silently rejecting those Word
    constructors as the stateless compiler above must do. -/

structure WordStackBitmapState where
  data : List Nat
  length : Nat
  deriving Repr

def wordStackInitialBitmaps (perf : Bool) : WordStackBitmapState :=
  if perf then
    { data := [16], length := 1 }
  else
    { data := [4], length := 1 }

def wordStackBitsToNat : List Bool → Nat
  | [] => 1
  | bit :: bits =>
      wordStackBitsToNat bits * 2 + if bit then 1 else 0

def wordStackBitmapChunk (constants : List (Bool × Nat)) : List Nat :=
  wordStackBitsToNat (constants.map Prod.fst) :: constants.map Prod.snd

def wordStackBitmapWordsAux (chunkSize : Nat) :
    Nat → List Bool → List Nat
  | 0, _ => []
  | fuel + 1, bits =>
      if chunkSize = 0 || bits.length ≤ chunkSize then
        [wordStackBitsToNat bits]
      else
        wordStackBitsToNat (bits.take chunkSize ++ [true]) ::
          wordStackBitmapWordsAux chunkSize fuel (bits.drop chunkSize)

def wordStackBitmapWords (chunkSize : Nat) (bits : List Bool) : List Nat :=
  wordStackBitmapWordsAux chunkSize (bits.length + 1) bits

def wordStackConstBitmapWordsAux (wordBits : Nat) :
    Nat → List (Bool × Nat) → List Nat
  | 0, _ => []
  | fuel + 1, constants =>
      let chunkSize := wordBits - 1
      if chunkSize = 0 || constants.length < chunkSize then
        wordStackBitmapChunk constants
      else
        wordStackBitmapChunk (constants.take chunkSize) ++
          wordStackConstBitmapWordsAux wordBits fuel (constants.drop chunkSize)

def wordStackConstBitmapWords (wordBits : Nat)
    (constants : List (Bool × Nat)) : List Nat :=
  wordStackConstBitmapWordsAux wordBits (constants.length + 1) constants

def wordStackLiveBitmap (registerCount frameSlots wordBits : Nat)
    (live : List Nat) : List Nat :=
  let names := live.map (fun register =>
    frameSlots - 1 - (register / 2 - registerCount))
  let bits := (List.range frameSlots).map (fun slot => names.contains slot)
  wordStackBitmapWords (wordBits - 1) (bits ++ [true])

/- Location-derived mirror of the original `write_bitmap`: one membership bit
    per frame slot for the live cut-set variables that the allocator actually
    placed on the stack, folded with the base-1 `wordStackBitsToNat` whose
    implicit top bit terminates the word.  Register-resident live values carry
    no stack root; the original's pancake artifacts pin the allocator to an
    empty stack live set there, keeping the words pure `2 ^ frameSlots`. -/
def wordStackLiveBitmapFromLocations (config : WordStackConfig)
    (frameSlots wordBits : Nat) (live : List Nat) : List Nat :=
  let slots := live.filterMap (fun name =>
    match wordStackLocation config name with
    | some (.stack slot) => some slot
    | _ => none)
  let bits := (List.range frameSlots).map (fun slot => slots.contains slot)
  wordStackBitmapWords (wordBits - 1) bits

def wordStackInsertBitmap (state : WordStackBitmapState)
    (bitmap : List Nat) : WordStackBitmapState × Nat :=
  ({ data := state.data ++ bitmap,
      length := state.length + bitmap.length }, state.length)

def wordStackBitmapWriteWithBuilder (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (bitmapBuilder : List Nat → List Nat) :
    StackProg Nat × WordStackBitmapState :=
  if frameSlots = 0 then
    (.skip, state)
  else
    let bitmap := bitmapBuilder live
    let (newState, index) := wordStackInsertBitmap state bitmap
    (.seq (.const bitmapRegister (index + 1))
        (.stackStore bitmapRegister (wordStackOffset config 0)), newState)

def wordStackAllocWithBitmapBuilder (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (bitmapBuilder : List Nat → List Nat) :
    StackProg Nat × WordStackBitmapState :=
  let (write, state) := wordStackBitmapWriteWithBuilder config bitmapRegister
    frameSlots state live bitmapBuilder
  (wordStackJoin write (.alloc 1), state)

def wordStackBitmapWrite (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (registerCount wordBits : Nat) :
    StackProg Nat × WordStackBitmapState :=
  wordStackBitmapWriteWithBuilder config bitmapRegister frameSlots state live
    (wordStackLiveBitmap registerCount frameSlots wordBits)

def wordStackAllocWithBitmaps (config : WordStackConfig)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (live : List Nat) (registerCount wordBits : Nat) :
    StackProg Nat × WordStackBitmapState :=
  wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state live
    (wordStackLiveBitmap registerCount frameSlots wordBits)

def wordStackStoreConstsWithBitmaps (_config : WordStackConfig)
    (registerCount specialScratch wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (constants : List (Bool × Nat)) :
    StackProg Nat × WordStackBitmapState :=
  let bitmap := wordStackConstBitmapWords wordBits constants
  let (newState, index) := wordStackInsertBitmap state bitmap
  (.seq (.const specialScratch index)
      (.storeConsts registerCount (registerCount + 1) storeConstsStub), newState)

def wordStackGet {α : Type} (config : WordStackConfig) (destination : Nat)
    (store : WordStore α) : Option (StackProg α) := do
  let store ← wordStackStoreName store
  let location ← wordStackLocation config destination
  match location with
  | .register register => pure (.get register store)
  | .stack slot =>
      pure (wordStackJoin (.get config.scratch store)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackOpCurrHeap {α : Type} (config : WordStackConfig) (operator : BinOp)
    (destination source : Nat) : Option (StackProg α) := do
  let (prelude, sourceRegister) ←
    wordStackReadRegister config source config.addressScratch
  let destination ← wordStackLocation config destination
  match destination with
  | .register destination =>
      pure (wordStackJoin prelude
        (.opCurrHeap operator destination sourceRegister))
  | .stack slot =>
      pure (wordStackJoin prelude
        (wordStackJoin
          (.opCurrHeap operator config.scratch sourceRegister)
          (.stackStore config.scratch (wordStackOffset config slot))))

def wordStackInstall {α : Type} (config : WordStackConfig)
    (codeBuffer codeLength dataBuffer dataLength : Nat) : Option (StackProg α) := do
  let codeBuffer ← wordStackLocation config codeBuffer
  let codeLength ← wordStackLocation config codeLength
  let dataBuffer ← wordStackLocation config dataBuffer
  let dataLength ← wordStackLocation config dataLength
  match codeBuffer, codeLength, dataBuffer, dataLength with
  | .register codeBuffer, .register codeLength,
      .register dataBuffer, .register dataLength =>
      pure (.install codeBuffer codeLength dataBuffer dataLength 0)
  | .register codeBuffer, .register codeLength,
      .stack dataBuffer, .register dataLength =>
      if codeBuffer = config.scratch || codeLength = config.scratch ||
          dataLength = config.scratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.scratch (wordStackOffset config dataBuffer))
          (.install codeBuffer codeLength config.scratch dataLength 0))
  | .register codeBuffer, .register codeLength,
      .register dataBuffer, .stack dataLength =>
      if codeBuffer = config.addressScratch ||
          codeLength = config.addressScratch ||
          dataBuffer = config.addressScratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config dataLength))
          (.install codeBuffer codeLength dataBuffer config.addressScratch 0))
  | .register codeBuffer, .register codeLength,
      .stack dataBuffer, .stack dataLength =>
      if codeBuffer = config.scratch || codeBuffer = config.addressScratch ||
          codeLength = config.scratch || codeLength = config.addressScratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.scratch (wordStackOffset config dataBuffer))
          (wordStackJoin
            (.stackLoad config.addressScratch (wordStackOffset config dataLength))
            (.install codeBuffer codeLength config.scratch config.addressScratch 0)))
  | _, _, _, _ => none

def wordStackBufferWrite {α : Type} (config : WordStackConfig) (isCode : Bool)
    (address value : Nat) : Option (StackProg α) := do
  let address ← wordStackLocation config address
  let value ← wordStackLocation config value
  match address, value with
  | .register address, .register value =>
      pure (if isCode then .codeBufferWrite address value
        else .dataBufferWrite address value)
  | .stack address, .register value =>
      if value = config.addressScratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config address))
          (if isCode then .codeBufferWrite config.addressScratch value
          else .dataBufferWrite config.addressScratch value))
  | .register address, .stack value =>
      if address = config.scratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.scratch (wordStackOffset config value))
          (if isCode then .codeBufferWrite address config.scratch
          else .dataBufferWrite address config.scratch))
  | .stack address, .stack value =>
      if config.scratch = config.addressScratch then
        none
      else
        pure (wordStackJoin
          (.stackLoad config.addressScratch (wordStackOffset config address))
          (wordStackJoin
            (.stackLoad config.scratch (wordStackOffset config value))
            (if isCode then .codeBufferWrite config.addressScratch config.scratch
            else .dataBufferWrite config.addressScratch config.scratch)))

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

def wordStackExpressionIsAtom : WordExp Nat → Bool
  | .const _ | .var _ | .lookup _ => true
  | .load _ | .op _ _ | .shift _ _ _ => false

/-! Registers that currently hold a variable of this function.  A register that
    is not the image of any allocated variable is dead from the allocator's
    point of view, so a nested expression may safely borrow it as an extra
    temporary. -/
def wordStackSavedRegisters (config : WordStackConfig) : List Nat :=
  config.locations.filterMap (fun entry =>
    match entry.2 with
    | .register register => some register
    | .stack _ => none)

/-! Extra expression temporaries drawn from allocator registers that hold no
    variable.  These are appended *after* the four reserved scratch registers,
    so shallow expressions keep the historical register choice and only deep
    nesting reaches into this list. -/
def wordStackFreeRegisters (config : WordStackConfig) (target : Nat) : List Nat :=
  let saved := wordStackSavedRegisters config
  wordAllocatableRegisters.filter (fun register =>
    register != target && saved.all (fun used => used != register))

/-! Compile a possibly nested expression into a physical register.  The
    earlier atom compiler is sufficient for most Word expressions, but global
    initialization and global reads produce nested address arithmetic.  Use a
    small, explicit pool of reserved registers for the two children of each
    binary node; each recursive child receives the remaining pool, so a child
    cannot clobber a sibling that has already been evaluated.  When a tree is
    deeper than the four reserved registers, the pool continues with allocator
    registers that hold no variable, so nesting depth is bounded by the live
    values rather than by the reserved pool. -/
def wordStackExpressionTemporaries (config : WordStackConfig)
    (target : Nat) : List Nat :=
  ([config.scratch, config.addressScratch, config.specialScratch, config.carryScratch]
    |>.filter (fun register => register != target))
  ++ wordStackFreeRegisters config target

def wordStackCompileExpToRegisterNat (config : WordStackConfig)
    (target : Nat) (available : List Nat) : WordExp Nat → Option (StackProg Nat)
  | .const value => some (.const target value)
  | .var name => do
      let (prelude, source) ← wordStackReadRegister config name target
      pure (wordStackJoin prelude
        (if source = target then .skip else .arith .or target source source))
  | .lookup store => do
      let store ← wordStackStoreNameNat store
      pure (.get target store)
  | .load address => do
      let address ← wordStackCompileExpToRegisterNat config target available address
      pure (.seq address (.inst (.mem .load target target)))
  | .op operator [left, right] => do
      if wordStackExpressionIsAtom left && wordStackExpressionIsAtom right then
        match right with
        | .const value =>
            /- Cake's `inst_select_exp` folds a valid immediate into the
               instruction (`Binop op tar temp (Imm w)`) instead of writing a
               constant register into the destination first, so keep the left
               operand in its own register and let the constant register fuse
               into the immediate in the Stack-to-Lab lowering. -/
            let leftTemporary := available.head?.getD config.addressScratch
            let (leftPrelude, leftRegister) ←
              wordStackAtomNat config leftTemporary left
            let constantRegister :=
              (available.filter (fun register => register != leftRegister)).head?.getD
                config.addressScratch
            pure (wordStackJoin leftPrelude
              (wordStackJoin (.const constantRegister value)
                (.arith operator target leftRegister constantRegister)))
        | _ =>
            let (leftPrelude, leftRegister) ← wordStackAtomNat config target left
            let rightTemporary := available.head?.getD config.addressScratch
            let (rightPrelude, rightRegister) ← wordStackAtomNat config rightTemporary right
            pure (wordStackJoin leftPrelude
              (wordStackJoin rightPrelude (.arith operator target leftRegister rightRegister)))
      else
        let rightTarget ← available.head?
        let remaining := available.tail
        let right ← wordStackCompileExpToRegisterNat config rightTarget remaining right
        let left ← wordStackCompileExpToRegisterNat config target remaining left
        pure (wordStackJoin right
          (wordStackJoin left (.arith operator target target rightTarget)))
  | .shift operator left right => do
      if wordStackExpressionIsAtom left && wordStackExpressionIsAtom right then
        if operator == .ror then
          let destinationRegister :=
            if target == config.scratch then
              (available.find? (fun register => register != config.scratch)).getD
                config.addressScratch
            else target
          let operandRegisters :=
            [config.addressScratch, config.specialScratch, config.carryScratch]
              |>.filter (fun register => register != destinationRegister)
          let leftTemporary := operandRegisters.head?.getD config.addressScratch
          let rightTemporary := operandRegisters.tail.head?.getD config.specialScratch
          let (leftPrelude, leftRegister) ← wordStackAtomNat config leftTemporary left
          let (rightPrelude, rightRegister) ←
            wordStackAtomNat config rightTemporary right
          let rotate :=
            .shift operator destinationRegister leftRegister rightRegister
          let body :=
            if destinationRegister = target then rotate
            else .seq rotate (.arith .or target destinationRegister destinationRegister)
          pure (wordStackJoin leftPrelude (wordStackJoin rightPrelude body))
        else
          let (leftPrelude, leftRegister) ← wordStackAtomNat config target left
          let rightTemporary := available.head?.getD config.addressScratch
          let (rightPrelude, rightRegister) ← wordStackAtomNat config rightTemporary right
          pure (wordStackJoin leftPrelude
            (wordStackJoin rightPrelude (.shift operator target leftRegister rightRegister)))
      else if operator == .ror then
        let destinationRegister :=
          if target == config.scratch then
            (available.find? (fun register => register != config.scratch)).getD
              config.addressScratch
          else target
        let pool :=
          available.filter (fun register =>
            register != destinationRegister && register != config.scratch)
        let rightTarget ← pool.head?
        let remaining := pool.tail
        let right ← wordStackCompileExpToRegisterNat config rightTarget remaining right
        let left ← wordStackCompileExpToRegisterNat config destinationRegister remaining left
        let rotate := .shift operator destinationRegister destinationRegister rightTarget
        let body :=
          if destinationRegister = target then rotate
          else .seq rotate (.arith .or target destinationRegister destinationRegister)
        pure (wordStackJoin right (wordStackJoin left body))
      else
        let rightTarget ← available.head?
        let remaining := available.tail
        let right ← wordStackCompileExpToRegisterNat config rightTarget remaining right
        let left ← wordStackCompileExpToRegisterNat config target remaining left
        pure (wordStackJoin right
          (wordStackJoin left (.shift operator target target rightTarget)))
  | .op operator (first :: rest) => do
      let firstCode ←
        wordStackCompileExpToRegisterNat config target available first
      rest.foldlM
        (fun accumulated argument => do
          let temporary ← available.head?
          let argumentCode ← wordStackCompileExpToRegisterNat config temporary
            available.tail argument
          pure (wordStackJoin accumulated
            (wordStackJoin argumentCode
              (.arith operator target target temporary))))
        firstCode
  | .op _ _ => none
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordStackCompileExpToPhysicalNat (config : WordStackConfig)
    (destination : Nat) (expression : WordExp Nat) : Option (StackProg Nat) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      wordStackCompileExpToRegisterNat config register
        (wordStackExpressionTemporaries config register) expression
  | .stack slot =>
      let code ← wordStackCompileExpToRegisterNat config config.scratch
        (wordStackExpressionTemporaries config config.scratch) expression
      pure (wordStackJoin code
        (.stackStore config.scratch (wordStackOffset config slot)))

/- A store has two simultaneously live results: its computed address and its
   value. Keep the other result's reserved register out of the recursive
   expression pool so evaluating a nested expression cannot destroy it. -/
def wordStackExpressionTemporariesExcluding (config : WordStackConfig)
    (target forbidden : Nat) : List Nat :=
  ([config.scratch, config.addressScratch, config.specialScratch, config.carryScratch]
    |>.filter (fun register => register != target && register != forbidden))
  ++ (wordStackFreeRegisters config target).filter
        (fun register => register != forbidden)

def wordStackCompileStoreNatNested (config : WordStackConfig) (address : WordExp Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let addressPrelude ← wordStackCompileExpToRegisterNat config config.addressScratch
    (wordStackExpressionTemporaries config config.addressScratch) address
  let valuePrelude ← wordStackCompileExpToRegisterNat config config.scratch
    (wordStackExpressionTemporariesExcluding config config.scratch config.addressScratch)
    value
  pure (wordStackJoin addressPrelude
    (wordStackJoin valuePrelude
      (.inst (.mem .store config.scratch config.addressScratch))))

def wordStackCompileLoadNatNested (config : WordStackConfig) (destination : Nat)
    (address : WordExp Nat) : Option (StackProg Nat) := do
  let addressPrelude ← wordStackCompileExpToRegisterNat config config.addressScratch
    (wordStackExpressionTemporaries config config.addressScratch) address
  let body ← wordStackWritePhysicalNat config destination
    (fun register => .inst (.mem .load register config.addressScratch))
  pure (wordStackJoin addressPrelude body)

def wordStackCompileSharedNat (config : WordStackConfig)
    (operator : WordMemOp) (destination : Nat) (address : WordExp Nat) :
    Option (StackProg Nat) := do
  match address with
  | .const _ | .var _ | .lookup _ =>
      let (addressPrelude, addressRegister) ←
        wordStackAtomNat config config.addressScratch address
      let body ← wordStackWritePhysicalNat config destination
        (fun register => .shMem operator register addressRegister)
      pure (wordStackJoin addressPrelude body)
  | _ =>
      let addressPrelude ←
        wordStackCompileExpToRegisterNat config config.addressScratch
          (wordStackExpressionTemporaries config config.addressScratch) address
      let body ← wordStackWritePhysicalNat config destination
        (fun register => .shMem operator register config.addressScratch)
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
  | .load address =>
      match address with
      | .const _ | .var _ | .lookup _ =>
          wordStackCompileLoadNat config destination address
      | _ => wordStackCompileLoadNatNested config destination address
  | .op operator [left, .const value] =>
      let immediate : Bool :=
        match operator with
        | .add => decide (value < 2 ^ 11)
        | .sub => decide (value ≤ 2 ^ 11)
        | .and | .or | .xor => false
      if immediate then do
        match ← wordStackLocation config destination with
        | .register register => do
            let leftPrelude ← wordStackCompileExpToRegisterNat config config.addressScratch
              (wordStackExpressionTemporaries config config.addressScratch) left
            let leftRegister := config.addressScratch
            if register == config.scratch || leftRegister == config.scratch then
              wordStackCompileBinaryNat config destination operator left (.const value)
            else
              pure (wordStackJoin leftPrelude
                (.seq (.const config.scratch value)
                  (.arith operator register leftRegister config.scratch)))
        | .stack _ =>
            wordStackCompileBinaryNat config destination operator left (.const value)
      else
        wordStackCompileBinaryNat config destination operator left (.const value)
  | .op operator [left, right] =>
      match left with
      | .const _ | .var _ | .lookup _ =>
          match right with
          | .const _ | .var _ | .lookup _ =>
              wordStackCompileBinaryNat config destination operator left right
          | _ =>
              wordStackCompileExpToPhysicalNat config destination (.op operator [left, right])
      | _ =>
          wordStackCompileExpToPhysicalNat config destination (.op operator [left, right])
  | .op operator arguments =>
      wordStackCompileExpToPhysicalNat config destination (.op operator arguments)
  | .shift operator left right =>
      if operator == .ror then
        wordStackCompileExpToPhysicalNat config destination (.shift operator left right)
      else
        match left with
        | .const _ | .var _ | .lookup _ =>
            match right with
            | .const _ | .var _ | .lookup _ =>
                wordStackCompileShiftNat config destination operator left right
            | _ =>
                wordStackCompileExpToPhysicalNat config destination (.shift operator left right)
        | _ =>
            wordStackCompileExpToPhysicalNat config destination (.shift operator left right)

def wordStackSetNat (config : WordStackConfig) (store : WordStore Nat)
    (value : WordExp Nat) : Option (StackProg Nat) := do
  let store ← wordStackStoreNameNat store
  let (prelude, register) ← wordStackAtomNat config config.scratch value
  pure (wordStackJoin prelude (.set store register))

def wordStackMoveFromPhysical {α : Type} (config : WordStackConfig)
    (destination source : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config destination
  match location with
  | .register register =>
      if register = source then pure .skip
      else pure (.arith .or register source source)
  | .stack slot =>
      pure (.seq (.arith .or config.scratch source source)
        (.stackStore config.scratch (wordStackOffset config slot)))

def wordStackMoveToPhysical {α : Type} (config : WordStackConfig)
    (source destination : Nat) : Option (StackProg α) := do
  let location ← wordStackLocation config source
  match location with
  | .register register =>
      if register = destination then pure .skip
      else pure (.arith .or destination register register)
  | .stack slot =>
      pure (.seq (.stackLoad config.scratch (wordStackOffset config slot))
        (.arith .or destination config.scratch config.scratch))

def wordStackLocationMove {α : Type} (config : WordStackConfig)
    (destination source : WordLocation) : Option (StackProg α) :=
  match destination, source with
  | .register destination, .register source =>
      if destination = source then some .skip
      else some (.arith .or destination source source)
  | .register destination, .stack slot =>
      pure (.stackLoad destination (wordStackOffset config slot))
  | .stack slot, .register source =>
      pure (.stackStore source (wordStackOffset config slot))
  | .stack destinationSlot, .stack sourceSlot =>
      if destinationSlot = sourceSlot then
        some .skip
      else
        pure (.seq (.stackLoad config.scratch
            (wordStackOffset config sourceSlot))
          (.stackStore config.scratch (wordStackOffset config destinationSlot)))

def wordStackLocationMoveToScratch {α : Type} (config : WordStackConfig)
    (source : WordLocation) : Option (StackProg α) :=
  match source with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or config.addressScratch register register)
  | .stack slot =>
      pure (.stackLoad config.addressScratch (wordStackOffset config slot))

def wordStackLocationMoveFromScratch {α : Type} (config : WordStackConfig)
    (destination : WordLocation) : Option (StackProg α) :=
  match destination with
  | .register register =>
      if register = config.scratch || register = config.addressScratch then
        none
      else
        pure (.arith .or register config.addressScratch config.addressScratch)
  | .stack slot =>
      pure (.stackStore config.addressScratch (wordStackOffset config slot))

def wordStackLocationMoveDestinations
    (moves : List (WordLocation × WordLocation)) : List WordLocation :=
  moves.map (fun move => move.1)

def wordStackLocationMoveRemoveDestination (destination : WordLocation) :
    List (WordLocation × WordLocation) → List (WordLocation × WordLocation) :=
  List.filter (fun move => move.1 != destination)

def wordStackLocationMoveReady (destinations : List WordLocation) :
    List (WordLocation × WordLocation) → Option (WordLocation × WordLocation)
  | [] => none
  | move :: moves =>
      if move.1 = move.2 || move.2 ∉ destinations then
        some move
      else
        wordStackLocationMoveReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

/-- Schedule a parallel move list over `WordLocation`s in CakeML dependency
    order.  As in `wordStackParallelMoveAux`, a move whose source is no longer a
    pending destination reads a value that no remaining move overwrites, so it
    is safe only to emit **last**; `wordStackLocationMoveReady` selects exactly
    such a move, and emitting it first would clobber a destination that a
    remaining move still has to read (e.g. `[a <- b, b <- c]` must emit
    `a <- b` before `b <- c`).  Cycles are handled by saving one source in the
    reserved address scratch register and restoring it afterwards, the same
    temporary-register idea as `parmove`. -/
def wordStackParallelLocationMoveAux {α : Type} (config : WordStackConfig) :
    Nat → List (WordLocation × WordLocation) → Option (StackProg α)
  | 0, _ => none
  | fuel + 1, moves =>
      let destinations := wordStackLocationMoveDestinations moves
      -- A reserved register may be a move destination as long as the
      -- scheduling below never has to borrow it as a temporary.  After the
      -- Cake-style single-instruction moves only a stack-to-stack move borrows
      -- `scratch`, and only an unbreakable cycle borrows `addressScratch`;
      -- rejecting every reserved destination up front refuses register-only
      -- programs that need no temporary at all.
      let stackToStack (move : WordLocation × WordLocation) : Bool :=
        match move.1, move.2 with
        | .stack _, .stack _ => true
        | _, _ => false
      let scratchBusy :=
        moves.any (fun (move : WordLocation × WordLocation) =>
          move.1 = WordLocation.register config.scratch)
      let addressScratchBusy :=
        moves.any (fun (move : WordLocation × WordLocation) =>
          move.1 = WordLocation.register config.addressScratch)
      if (moves.any stackToStack && scratchBusy) ||
          (addressScratchBusy && (wordStackLocationMoveReady destinations moves).isNone) then
        none
      else if !destinations.Nodup then
        none
      else if moves.isEmpty then
        some .skip
      else
        match wordStackLocationMoveReady destinations moves with
        | some (destination, source) => do
            let rest ← wordStackParallelLocationMoveAux config fuel
              (wordStackLocationMoveRemoveDestination destination moves)
            let last ← wordStackLocationMove config destination source
            pure (wordStackJoin rest last)
        | none =>
            match moves with
            | [] => some .skip
            | (destination, source) :: _ => do
                if config.scratch = config.addressScratch then none else
                  let save ← wordStackLocationMoveToScratch config source
                  let rest ← wordStackParallelLocationMoveAux config fuel
                    (wordStackLocationMoveRemoveDestination destination moves)
                  let restore ← wordStackLocationMoveFromScratch config destination
                  pure (wordStackJoin save (wordStackJoin rest restore))

def wordStackParallelLocationMove {α : Type} (config : WordStackConfig)
    (moves : List (WordLocation × WordLocation)) : Option (StackProg α) :=
  wordStackParallelLocationMoveAux config (moves.length + 1) moves

/-- Materialize the four FFI arguments into the fixed RISC-V ABI registers
    x10--x13.  When the sources already avoid those registers we keep the
    original sequential move chain; otherwise we fall back to a parallel move
    so a source that already lives in one of the destination registers is not
    clobbered before it is read. -/
def wordStackFfi {α : Type} (config : WordStackConfig) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    Option (StackProg α) := do
  let sources := [configuration, configurationLength, array, arrayLength]
  if wordStackFfiSourcesSafe config sources then
    let configurationMove ← wordStackFfiMove config configuration 10
    let configurationLengthMove ← wordStackFfiMove config configurationLength 11
    let arrayMove ← wordStackFfiMove config array 12
    let arrayLengthMove ← wordStackFfiMove config arrayLength 13
    pure (wordStackJoin configurationMove
      (wordStackJoin configurationLengthMove
        (wordStackJoin arrayMove
          (wordStackJoin arrayLengthMove
            (.ffi function 10 11 12 13 0)))))
  else
    let configurationLocation ← wordStackLocation config configuration
    let configurationLengthLocation ← wordStackLocation config configurationLength
    let arrayLocation ← wordStackLocation config array
    let arrayLengthLocation ← wordStackLocation config arrayLength
    let moves : List (WordLocation × WordLocation) :=
      [ (.register 10, configurationLocation),
        (.register 11, configurationLengthLocation),
        (.register 12, arrayLocation),
        (.register 13, arrayLengthLocation) ]
    let prelude ← wordStackParallelLocationMove config moves
    pure (.seq prelude (.ffi function 10 11 12 13 0))

def wordStackPhysicalMovesFrom (config : WordStackConfig) :
    List Nat → Nat → Option (List (WordLocation × WordLocation))
  | [], _ => some []
  | destination :: destinations, source => do
      let destination ← wordStackLocation config destination
      let rest ← wordStackPhysicalMovesFrom config destinations
        (source + config.abiStride)
      pure ((destination, .register source) :: rest)
termination_by destinations => sizeOf destinations
decreasing_by all_goals decreasing_trivial

/-! Argument moves start at the ABI base the caller supplied, so the
    overflow index must be counted from that same base.  The stride is
    carried by the index (`wMoveSingle`'s `f - 1 - (r - k)` numbering is
    consecutive for RISC-V), so the recursion deliberately keeps the base
    fixed: advancing it as well double-counted the stride and put the
    second argument one register too high. -/
def wordStackPhysicalMovesToIndexed (config : WordStackConfig) :
    Nat → List Nat → Nat → Option (List (WordLocation × WordLocation))
  | _, [], _ => some []
  | index, source :: sources, base => do
      let source ← wordStackLocation config source
      let destinationLocation :=
        if config.abiFrameSlots = 0 then
          .register (base + config.abiStride * index)
        else
          wordStackPhysicalLocation config index base
      let rest ← wordStackPhysicalMovesToIndexed config (index + 1) sources base
      pure ((destinationLocation, source) :: rest)
  termination_by _ sources _ => sizeOf sources
  decreasing_by all_goals decreasing_trivial

def wordStackPhysicalMovesTo (config : WordStackConfig) :
    List Nat → Nat → Option (List (WordLocation × WordLocation))
  | sources, base => wordStackPhysicalMovesToIndexed config 0 sources base

def wordStackMovesFromPhysical {α : Type} (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | destinations, source => do
      let moves ← wordStackPhysicalMovesFrom config destinations source
      wordStackParallelLocationMove config moves

/-! Entry parameters are Word names, while the RISC-V ABI source registers
    are supplied by the target register-name map.  In particular Cake maps
    Word slot 0 to the link register, so a source-shaped function must not
    treat every entry slot as a consecutive ordinary argument register. -/
def wordStackPhysicalMovesFromSources (config : WordStackConfig) :
    List Nat → List Nat → Option (List (WordLocation × WordLocation))
  | [], [] => some []
  | destination :: destinations, source :: sources => do
      let destination ← wordStackLocation config destination
      let rest ← wordStackPhysicalMovesFromSources config destinations sources
      pure ((destination, .register source) :: rest)
  | _, _ => none

def wordStackMovesFromPhysicalSources {α : Type} (config : WordStackConfig)
    (destinations : List Nat) (sources : List Nat) : Option (StackProg α) := do
  let moves ← wordStackPhysicalMovesFromSources config destinations sources
  wordStackParallelLocationMove config moves

def wordStackMovesToPhysical {α : Type} (config : WordStackConfig) :
    List Nat → Nat → Option (StackProg α)
  | sources, destination => do
      let moves ← wordStackPhysicalMovesTo config sources destination
      wordStackParallelLocationMove config moves

def wordStackReturnCode {α : Type} (config : WordStackConfig) :
    Option (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat) →
      Option (StackProg α)
  | none => some .skip
  | some (destinations, _, _, _, _) =>
      wordStackMovesFromPhysical config destinations config.abiBase

/-! The `Return v1 vs` case in Cake's `comp` frees the part of the current
    frame occupied by returned values which do not fit in the ABI result
    registers.  Flapjack stores all returned values in one list (where Cake
    stores `v1` separately from `vs`), so the corresponding count is
    `f - (LENGTH values - k)`. -/
def wordStackReturnFreeCount (config : WordStackConfig) (values : List Nat) : Nat :=
  wordStackCakeFrameSize config - (values.length - config.abiRegisterCount)

/-! Cake's `wReg1` emits a `StackLoad` when the return address has been
    spilled to the frame, jumping through the spare register afterwards.  The
    register-bearing return therefore loads a frame-allocated link value back
    before the jump, and falls back to the link register when the return
    variable has no location at all (matching the hardcoded `ret` of the
    earlier port). -/
def wordStackReturn {α : Type} (config : WordStackConfig) (returnLabel : Nat) (values : List Nat) :
    Option (StackProg α) := do
  let moves ← wordStackMovesToPhysical config values config.abiBase
  let (loads, returnRegister) ← match wordStackLocation config returnLabel with
    | some (.register register) => pure ((.skip : StackProg α), register)
    | some (.stack slot) =>
        pure ((.stackLoad config.scratch (wordStackOffset config slot)),
          config.scratch)
    | none => pure ((.skip : StackProg α), 0)
  match values with
  | [] => pure moves
  | _ => pure (wordStackJoin moves
      (wordStackJoin loads
        (stackFreeIfNonzero (wordStackReturnFreeCount config values)
          (.return returnRegister))))

def wordToStackInst {α : Type} (config : WordStackConfig) : WordInst α → Option (StackProg α)
  | .const destination value => some (.inst (.const destination value))
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

def evalWordStackBasic {α : Type} [NeZero width] (state : WordStackState width) :
    StackProg α → Option (WordStackState width)
  | .skip => some state
  | .arith .or destination left right =>
      some (wordStackWriteRegister state destination
        (state.registers left ||| state.registers right))
  | .stackLoad register offset =>
      some (wordStackWriteRegister state register (state.stack offset))
  | .stackStore register offset =>
      some (wordStackWriteSlot state offset (state.registers register))
  | .tick => some state
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

/-! The StackLang `LongDiv` operation follows CakeML's word convention: the
    two source words form one unsigned double-width dividend, the divisor must
    be nonzero, and the quotient must fit in one word.  Returning `none` for
    either failed precondition matches the source/StackLang semantics. -/
def wordStackLongDivResult [NeZero width]
    (sourceLeft sourceRight divisor : Word width) :
    Option (Word width × Word width) :=
  let divisorValue := divisor.toNat
  let dividendValue := sourceLeft.toNat * 2 ^ width + sourceRight.toNat
  if divisorValue == 0 then
    none
  else
    let quotient := dividendValue / divisorValue
    if quotient < 2 ^ width then
      some (BitVec.ofNat width quotient,
        BitVec.ofNat width (dividendValue % divisorValue))
    else
      none

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
  | .inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) =>
      let left := state.registers sourceLeft
      let right := state.registers sourceRight
      let high := BitVec.ofNat width (left.toNat * right.toNat / 2 ^ width)
      let state := wordStackMachineWriteRegister state destinationLeft high
      some (wordStackMachineWriteRegister state destinationRight (left * right))
  | .inst (.arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight divisor)) =>
      match wordStackLongDivResult (state.registers sourceLeft)
          (state.registers sourceRight) (state.registers divisor) with
      | some (quotient, remainder) =>
          let state := wordStackMachineWriteRegister state destinationLeft quotient
          some (wordStackMachineWriteRegister state destinationRight remainder)
      | none => none
  | .inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)) =>
      let left := state.registers sourceLeft
      let right := state.registers sourceRight
      let carry := if state.registers carryIn == 0 then 0 else 1
      let total := left.toNat + right.toNat + carry
      let state := wordStackMachineWriteRegister state destination
        (BitVec.ofNat width total)
      some (wordStackMachineWriteRegister state resultCarry
        (BitVec.ofNat width (total / 2 ^ width)))
  | .inst (.arith (.cakeAddCarry destination sourceLeft sourceRight carry)) =>
      let left := state.registers sourceLeft
      let right := state.registers sourceRight
      let carryIn := if state.registers carry == 0 then 0 else 1
      let total := left.toNat + right.toNat + carryIn
      let state := wordStackMachineWriteRegister state destination
        (BitVec.ofNat width total)
      some (wordStackMachineWriteRegister state carry
        (BitVec.ofNat width (total / 2 ^ width)))
  | .inst (.arith (.div destination dividend divisor)) =>
      let divisorValue := state.registers divisor
      let value := if divisorValue == 0 then
        BitVec.ofNat width (2 ^ width - 1)
      else
        BitVec.ofNat width (state.registers dividend).toNat / divisorValue.toNat
      some (wordStackMachineWriteRegister state destination value)
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
  | .tick => some state
  | .seq first second => do
      let state ← evalWordStackMachine state first
      evalWordStackMachine state second
  | .ite operator condition right thenBranch elseBranch =>
      let rightValue := match right with
        | .imm value => BitVec.ofNat width value
        | .reg register => state.registers register
      let conditionHolds := match operator with
        | .equal => state.registers condition == rightValue
        | .notEqual => state.registers condition != rightValue
        | .lower => decide (state.registers condition < rightValue)
        | .notLower => decide (¬ state.registers condition < rightValue)
        | .less => signedLess (state.registers condition) rightValue
        | .notLess => !signedLess (state.registers condition) rightValue
        | .test => state.registers condition &&& rightValue == 0
        | .notTest => state.registers condition &&& rightValue != 0
      if conditionHolds then
        evalWordStackMachine state thenBranch
      else
        evalWordStackMachine state elseBranch
  | _ => none

def wordStackMachineValue [NeZero width] (config : WordStackConfig)
    (state : WordStackMachineState width) (name : Nat) : Option (Word width) := do
  let location ← wordStackLocation config name
  match location with
  | .register register => some (state.registers register)
  | .stack slot => some (state.stack (wordStackOffset config slot))

def wordStackBinaryLocationsSafe (config : WordStackConfig) :
    WordLocation → WordLocation → Bool
  | .register _, .register _ => true
  | .register left, .stack _ => left != config.addressScratch
  | .stack _, .register right => right != config.scratch
  | .stack _, .stack _ => config.scratch != config.addressScratch

theorem evalWordStackMachine_const_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination value : Nat) (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (heval : (wordStackCompileExpNat config destination (.const value)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (BitVec.ofNat width value) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  simp [wordStackCompileExpNat, wordStackWritePhysicalNat] at heval
  cases destinationLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister, 
      hdestination] at heval ⊢
  all_goals
    cases heval
    simp [
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat) (destinationLocation sourceLocation : WordLocation)
    (hdestination : wordStackLocation config destination = some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestinationScratch : destinationLocation ≠ .register config.scratch)
    (hsourceScratch : sourceLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        wordStackMachineValue config state source := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases destinationLocation <;> cases sourceLocation <;>
    simp [wordStackMove, evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, hsource,
      ] at heval ⊢
  all_goals
    try split at heval <;>
    simp_all [evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot]
    cases heval
    simp [
      
      wordStackMachineBinOp,
      ]

theorem evalWordStackMachine_lookup_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination : Nat) (store : WordStore Nat) (stackStore : StackStore)
    (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (heval : (wordStackCompileExpNat config destination (.lookup store)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.stores stackStore) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases destinationLocation <;>
      simp [wordStackCompileExpNat, wordStackStoreNameNat,
        wordStackWritePhysicalNat] at heval
  all_goals
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      hdestination] at heval ⊢
  all_goals
    cases heval
    simp [
      wordStackMachineWriteRegister, wordStackMachineWriteSlot]

theorem evalWordStackMachine_set_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (store : WordStore Nat) (stackStore : StackStore) (source : Nat)
    (sourceLocation : WordLocation) (sourceValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (hstore : wordStackStoreNameNat store = some stackStore)
    (heval : (wordStackSetNat config store (.var source)).bind
      (evalWordStackMachine state) = some final) :
      final.stores stackStore = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases store <;> simp [wordStackStoreNameNat] at hstore
  all_goals
    cases hstore
    cases sourceLocation <;>
    simp [wordStackSetNat, wordStackStoreNameNat, wordStackAtomNat,
      wordStackReadRegister, wordStackLocation, wordStackOffset,
      wordStackJoin, evalWordStackMachine, hsource] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource] at hsourceValue
    simp [wordStackMachineWriteRegister, wordStackMachineWriteStore,
      hsourceValue]

theorem evalWordStackMachine_binary_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : BinOp) (destination left right : Nat)
    (destinationLocation leftLocation rightLocation : WordLocation)
    (leftValue rightValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hleftValue : wordStackMachineValue config state left = some leftValue)
    (hrightValue : wordStackMachineValue config state right = some rightValue)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
    (heval : (wordStackCompileBinaryNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (wordStackMachineBinOp operator leftValue rightValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo left config.locations = some leftLocation at hleft
  change lookupNatInfo right config.locations = some rightLocation at hright
  cases destinationLocation <;> cases leftLocation <;> cases rightLocation <;>
    simp [wordStackCompileBinaryNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, hleft, hright, wordStackBinaryLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hleft, hright] at hleftValue hrightValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      wordStackMachineBinOp, hdestination, hleftValue, hrightValue, hsafe]

theorem evalWordStackMachine_shift_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (operator : Shift) (destination left right : Nat)
    (destinationLocation leftLocation rightLocation : WordLocation)
    (leftValue rightValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hleft : wordStackLocation config left = some leftLocation)
    (hright : wordStackLocation config right = some rightLocation)
    (hleftValue : wordStackMachineValue config state left = some leftValue)
    (hrightValue : wordStackMachineValue config state right = some rightValue)
    (hsafe : wordStackBinaryLocationsSafe config leftLocation rightLocation = true)
    (heval : (wordStackCompileShiftNat config destination operator
      (.var left) (.var right)).bind (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (wordStackMachineShift operator leftValue rightValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo left config.locations = some leftLocation at hleft
  change lookupNatInfo right config.locations = some rightLocation at hright
  cases destinationLocation <;> cases leftLocation <;> cases rightLocation <;>
    simp [wordStackCompileShiftNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, hleft, hright, wordStackBinaryLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hleft, hright] at hleftValue hrightValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      wordStackMachineShift, hdestination, hleftValue, hrightValue, hsafe]

theorem evalWordStackMachine_load_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (addressValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (_hscratch : config.scratch ≠ config.addressScratch)
    (heval : (wordStackCompileLoadNat config destination (.var address)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.memory addressValue) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackCompileLoadNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, evalWordStackMachine, wordStackJoin,
      wordStackLocation, wordStackOffset, 
      hdestination, haddress] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      haddress] at haddressValue
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      haddressValue, hdestination]

theorem evalWordStackMachine_load_const_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat) (destinationLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (heval : (wordStackCompileLoadNat config destination (.const address)).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (state.memory (BitVec.ofNat width address)) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  cases destinationLocation <;>
    simp [wordStackCompileLoadNat, wordStackAtomNat, wordStackWritePhysicalNat,
      evalWordStackMachine, wordStackJoin, wordStackLocation,
      wordStackOffset, hdestination] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, hdestination]

theorem evalWordStackMachine_store_assignment [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackCompileStoreNat config (.var address) (.var source)).bind
      (evalWordStackMachine state) = some final) :
      final.memory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackCompileStoreNat, wordStackAtomNat, wordStackReadRegister,
      wordStackJoin, evalWordStackMachine, wordStackLocation, wordStackOffset,
      hsource, haddress, wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteMemory, hsourceValue,
      haddressValue, hsafe, hsafe']

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
  cases destinationLocation <;> cases sourceLocation <;>
    simp [wordStackMove, evalWordStackBasic, wordStackValue, wordStackLocation,
      wordStackOffset, wordStackWriteRegister, wordStackWriteSlot,
      hdestination, hsource] at heval ⊢
  all_goals
    try split at heval <;>
    simp_all [evalWordStackBasic, wordStackWriteRegister, wordStackWriteSlot]
    cases heval
    simp [
      
      ]

theorem evalWordStackBasic_move_to_physical_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackState width)
    (source destination : Nat) (sourceLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (heval : (wordStackMoveToPhysical (α := Nat) config source destination).bind
      (evalWordStackBasic state) = some final) :
      final.registers destination = wordStackValue config state source := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      by_cases hsame : register = destination
      · simp [wordStackMoveToPhysical, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        simp [wordStackValue, wordStackLocation, 
          hsource, hsame]
      · simp [wordStackMoveToPhysical, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        simp [wordStackValue, wordStackLocation,
          wordStackWriteRegister, hsource]
  | stack slot =>
      simp [wordStackMoveToPhysical, wordStackLocation, 
        hsource] at heval
      cases heval
      simp [wordStackValue, wordStackLocation,
        wordStackOffset, wordStackWriteRegister, hsource]

theorem evalWordStackMachine_ffi_move_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination : Nat) (sourceLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination : sourceLocation ≠ .register destination)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
      final.registers destination = wordStackMachineValue config state source := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register register =>
      have hregister : register ≠ destination := by
        intro heq
        apply hdestination
        simp [heq]
      simp [wordStackFfiMove, wordStackLocation, 
        hsource, hregister] at heval
      cases heval
      simp [wordStackMachineValue, wordStackLocation,
        wordStackMachineWriteRegister, wordStackMachineBinOp, hsource,
        ]
  | stack slot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at heval
      cases heval
      simp [wordStackMachineValue,
        wordStackLocation, wordStackOffset, wordStackMachineWriteRegister,
        hsource]

theorem evalWordStackMachine_ffi_move_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination other : Nat) (sourceLocation otherLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hsource_destination : sourceLocation ≠ .register destination)
    (hother_destination : otherLocation ≠ .register destination)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final other =
        wordStackMachineValue config state other := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  cases sourceLocation with
  | register sourceRegister =>
      have hsourceRegister : sourceRegister ≠ destination := by
        intro heq
        apply hsource_destination
        simp [heq]
      simp [wordStackFfiMove, wordStackLocation, 
        hsource, hsourceRegister] at heval
      cases heval
      cases otherLocation with
      | register otherRegister =>
          have hotherRegister : otherRegister ≠ destination := by
            intro heq
            apply hother_destination
            simp [heq]
          simp [wordStackMachineValue, wordStackLocation,
            wordStackMachineWriteRegister, wordStackMachineBinOp, hother,
            hotherRegister]
      | stack otherSlot =>
          simp [wordStackMachineValue, wordStackLocation,
            wordStackMachineWriteRegister, wordStackMachineBinOp, hother]
  | stack sourceSlot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at heval
      cases heval
      cases otherLocation with
      | register otherRegister =>
          have hotherRegister : otherRegister ≠ destination := by
            intro heq
            apply hother_destination
            simp [heq]
          simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
            wordStackMachineWriteRegister, hother, hotherRegister]
      | stack otherSlot =>
          simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
            wordStackMachineWriteRegister, hother]

theorem evalWordStackMachine_ffi_move_preserves_register [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source destination register : Nat) (sourceLocation : WordLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination : destination ≠ register)
    (heval : (wordStackFfiMove config source destination).bind
      (evalWordStackMachine state) = some final) :
      final.registers register = state.registers register := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  cases sourceLocation with
  | register sourceRegister =>
      by_cases hsame : sourceRegister = destination
      · simp [wordStackFfiMove, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        rfl
      · simp [wordStackFfiMove, wordStackLocation, 
          hsource, hsame] at heval
        cases heval
        have hregister : register ≠ destination := by
          intro heq
          exact hdestination heq.symm
        simp [wordStackMachineWriteRegister, wordStackMachineBinOp,
          hregister]
  | stack sourceSlot =>
      simp [wordStackFfiMove, wordStackLocation, 
        hsource] at heval
      cases heval
      have hregister : register ≠ destination := by
        intro heq
        apply hdestination
        exact heq.symm
      simp [wordStackMachineWriteRegister, hregister]

theorem evalWordStackMachine_ffi_argument_moves [NeZero width]
    (config : WordStackConfig)
    (state state1 state2 state3 final : WordStackMachineState width)
    (configuration configurationLength array arrayLength : Nat)
    (configurationLocation configurationLengthLocation arrayLocation
      arrayLengthLocation : WordLocation)
    (hconfiguration : wordStackLocation config configuration =
      some configurationLocation)
    (hconfigurationLength : wordStackLocation config configurationLength =
      some configurationLengthLocation)
    (harray : wordStackLocation config array = some arrayLocation)
    (harrayLength : wordStackLocation config arrayLength =
      some arrayLengthLocation)
    (hsafe : ∀ location, location ∈
      [configurationLocation, configurationLengthLocation, arrayLocation,
        arrayLengthLocation] →
      ∀ destination, destination ∈ [10, 11, 12, 13] →
        location ≠ .register destination)
    (hevalConfiguration :
      (wordStackFfiMove config configuration 10).bind
        (evalWordStackMachine state) = some state1)
    (hevalConfigurationLength :
      (wordStackFfiMove config configurationLength 11).bind
        (evalWordStackMachine state1) = some state2)
    (hevalArray :
      (wordStackFfiMove config array 12).bind
        (evalWordStackMachine state2) = some state3)
    (hevalArrayLength :
      (wordStackFfiMove config arrayLength 13).bind
        (evalWordStackMachine state3) = some final) :
    some (final.registers 10) = wordStackMachineValue config state configuration ∧
    some (final.registers 11) = wordStackMachineValue config state configurationLength ∧
    some (final.registers 12) = wordStackMachineValue config state array ∧
    some (final.registers 13) = wordStackMachineValue config state arrayLength := by
  have hconfiguration10 := hsafe configurationLocation (by simp) 10 (by simp)
  have hconfigurationLength10 :=
    hsafe configurationLengthLocation (by simp) 10 (by simp)
  have hconfigurationLength11 :=
    hsafe configurationLengthLocation (by simp) 11 (by simp)
  have harray10 := hsafe arrayLocation (by simp) 10 (by simp)
  have harray11 := hsafe arrayLocation (by simp) 11 (by simp)
  have harray12 := hsafe arrayLocation (by simp) 12 (by simp)
  have harrayLength10 := hsafe arrayLengthLocation (by simp) 10 (by simp)
  have harrayLength11 := hsafe arrayLengthLocation (by simp) 11 (by simp)
  have harrayLength12 := hsafe arrayLengthLocation (by simp) 12 (by simp)
  have harrayLength13 := hsafe arrayLengthLocation (by simp) 13 (by simp)
  have hconfigurationValue := evalWordStackMachine_ffi_move_preserves_value
    config state state1 configuration 10 configurationLocation
    hconfiguration hconfiguration10 hevalConfiguration
  have hconfigurationLengthValue :=
    evalWordStackMachine_ffi_move_preserves_other_value config state state1
      configuration 10 configurationLength configurationLocation
      configurationLengthLocation hconfiguration hconfigurationLength
      hconfiguration10 hconfigurationLength10 hevalConfiguration
  have harrayValue1 := evalWordStackMachine_ffi_move_preserves_other_value
    config state state1 configuration 10 array configurationLocation arrayLocation
    hconfiguration harray hconfiguration10 harray10 hevalConfiguration
  have harrayValue2 := evalWordStackMachine_ffi_move_preserves_other_value
    config state1 state2 configurationLength 11 array
      configurationLengthLocation arrayLocation hconfigurationLength harray
      hconfigurationLength11 harray11 hevalConfigurationLength
  have harrayLengthValue1 := evalWordStackMachine_ffi_move_preserves_other_value
    config state state1 configuration 10 arrayLength configurationLocation
      arrayLengthLocation hconfiguration harrayLength hconfiguration10
      harrayLength10 hevalConfiguration
  have harrayLengthValue2 := evalWordStackMachine_ffi_move_preserves_other_value
    config state1 state2 configurationLength 11 arrayLength
      configurationLengthLocation arrayLengthLocation hconfigurationLength
      harrayLength hconfigurationLength11 harrayLength11
      hevalConfigurationLength
  have harrayLengthValue3 := evalWordStackMachine_ffi_move_preserves_other_value
    config state2 state3 array 12 arrayLength arrayLocation arrayLengthLocation
      harray harrayLength harray12 harrayLength12 hevalArray
  have hconfigurationLengthRegister :=
    evalWordStackMachine_ffi_move_preserves_value config state1 state2
      configurationLength 11 configurationLengthLocation hconfigurationLength
      hconfigurationLength11 hevalConfigurationLength
  have harrayRegister := evalWordStackMachine_ffi_move_preserves_value
    config state2 state3 array 12 arrayLocation harray harray12 hevalArray
  have harrayLengthRegister := evalWordStackMachine_ffi_move_preserves_value
    config state3 final arrayLength 13 arrayLengthLocation harrayLength
      harrayLength13 hevalArrayLength
  have h10_2 := evalWordStackMachine_ffi_move_preserves_register config state1
    state2 configurationLength 11 10 configurationLengthLocation
    hconfigurationLength (by decide) hevalConfigurationLength
  have h10_3 := evalWordStackMachine_ffi_move_preserves_register config state2
    state3 array 12 10 arrayLocation harray (by decide) hevalArray
  have h10_4 := evalWordStackMachine_ffi_move_preserves_register config state3
    final arrayLength 13 10 arrayLengthLocation harrayLength (by decide)
    hevalArrayLength
  have h11_3 := evalWordStackMachine_ffi_move_preserves_register config state2
    state3 array 12 11 arrayLocation harray (by decide) hevalArray
  have h11_4 := evalWordStackMachine_ffi_move_preserves_register config state3
    final arrayLength 13 11 arrayLengthLocation harrayLength (by decide)
    hevalArrayLength
  have h12_4 := evalWordStackMachine_ffi_move_preserves_register config state3
    final arrayLength 13 12 arrayLengthLocation harrayLength (by decide)
    hevalArrayLength
  constructor
  · calc
      some (final.registers 10) = some (state3.registers 10) := congrArg some h10_4
      _ = some (state2.registers 10) := congrArg some h10_3
      _ = some (state1.registers 10) := congrArg some h10_2
      _ = wordStackMachineValue config state configuration := hconfigurationValue
  · constructor
    · calc
        some (final.registers 11) = some (state3.registers 11) := congrArg some h11_4
        _ = some (state2.registers 11) := congrArg some h11_3
        _ = wordStackMachineValue config state1 configurationLength :=
          hconfigurationLengthRegister
        _ = wordStackMachineValue config state configurationLength :=
          hconfigurationLengthValue
    · constructor
      · calc
          some (final.registers 12) = some (state3.registers 12) := congrArg some h12_4
          _ = wordStackMachineValue config state2 array := harrayRegister
          _ = wordStackMachineValue config state1 array := harrayValue2
          _ = wordStackMachineValue config state array := harrayValue1
      · calc
          some (final.registers 13) = wordStackMachineValue config state3 arrayLength :=
            harrayLengthRegister
          _ = wordStackMachineValue config state2 arrayLength :=
            harrayLengthValue3
          _ = wordStackMachineValue config state1 arrayLength :=
            harrayLengthValue2
          _ = wordStackMachineValue config state arrayLength :=
            harrayLengthValue1

theorem evalWordStackMachine_load_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (_hscratch : config.scratch ≠ config.addressScratch)
    (heval : (wordStackMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        (wordStackMachineValue config state address).map state.memory := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackMemoryInst, wordStackLoadInst, wordStackLocation,
      wordStackOffset, hdestination, haddress,
      ] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, haddress]

theorem evalWordStackMachine_store_preserves_memory [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
      final.memory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
      wordStackOffset, hsource, haddress,
      wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteMemory, hsourceValue,
      haddressValue, hsafe, hsafe']

theorem evalWordStackMachine_shared_load_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination address : Nat)
    (destinationLocation addressLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (heval : (wordStackSharedMemoryInst config .load destination address).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        (wordStackMachineValue config state address).map state.sharedMemory := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo address config.locations = some addressLocation at haddress
  cases destinationLocation <;> cases addressLocation <;>
    simp [wordStackSharedMemoryInst, wordStackSharedLoadInst,
      wordStackLocation, wordStackOffset, hdestination,
      haddress] at heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, 
      hdestination, haddress]

theorem evalWordStackMachine_shared_store_preserves_memory [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (source address : Nat)
    (sourceLocation addressLocation : WordLocation)
    (sourceValue addressValue : Word width)
    (hsource : wordStackLocation config source = some sourceLocation)
    (haddress : wordStackLocation config address = some addressLocation)
    (hsourceValue : wordStackMachineValue config state source =
      some sourceValue)
    (haddressValue : wordStackMachineValue config state address =
      some addressValue)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hsafe : wordStackStoreLocationsSafe config sourceLocation addressLocation = true)
    (heval : (wordStackSharedMemoryInst config .store source address).bind
      (evalWordStackMachine state) = some final) :
      final.sharedMemory addressValue = sourceValue := by
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo address config.locations = some addressLocation at haddress
  have hsafe' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases sourceLocation <;> cases addressLocation <;>
    simp [wordStackSharedMemoryInst, wordStackSharedStoreInst,
      wordStackLocation, wordStackOffset, hsource, haddress,
      wordStackStoreLocationsSafe] at hsafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hsource, haddress] at hsourceValue haddressValue
    simp [
      wordStackMachineWriteRegister, 
      wordStackMachineWriteSharedMemory, 
      hsourceValue, haddressValue, hsafe, hsafe']

theorem evalWordStackMachine_div_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination dividend divisor : Nat)
    (destinationLocation dividendLocation divisorLocation : WordLocation)
    (dividendValue divisorValue : Word width)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hdividend : wordStackLocation config dividend = some dividendLocation)
    (hdivisor : wordStackLocation config divisor = some divisorLocation)
    (hdividendValue : wordStackMachineValue config state dividend =
      some dividendValue)
    (hdivisorValue : wordStackMachineValue config state divisor =
      some divisorValue)
    (hdivisorNonzero : divisorValue ≠ 0)
    (hscratch : config.scratch ≠ config.addressScratch)
    (hdestinationSafe : wordStackDivLocationSafe config destinationLocation = true)
    (hdividendSafe : wordStackDivLocationSafe config dividendLocation = true)
    (hdivisorSafe : wordStackDivLocationSafe config divisorLocation = true)
    (heval : (wordStackDivInst config destination dividend divisor).bind
      (evalWordStackMachine state) = some final) :
      wordStackMachineValue config final destination =
        some (BitVec.ofNat width (dividendValue.toNat / divisorValue.toNat)) := by
  change lookupNatInfo destination config.locations = some destinationLocation at hdestination
  change lookupNatInfo dividend config.locations = some dividendLocation at hdividend
  change lookupNatInfo divisor config.locations = some divisorLocation at hdivisor
  have hscratch' : config.addressScratch ≠ config.scratch := by
    intro heq
    apply hscratch
    exact heq.symm
  cases destinationLocation <;> cases dividendLocation <;> cases divisorLocation <;>
    simp [wordStackDivInst, wordStackJoin, wordStackLocation, wordStackOffset,
      hdestination, hdividend, hdivisor,
      wordStackDivLocationSafe] at hdestinationSafe hdividendSafe hdivisorSafe heval
  all_goals
    cases heval
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      
      hdividend, hdivisor] at hdividendValue hdivisorValue
    have hdivisorNonzero' : ¬divisorValue = (0#width) := by
      intro hz
      apply hdivisorNonzero
      simpa using hz
    simp [wordStackMachineValue, wordStackLocation, wordStackOffset,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      hdestination, hdividendValue, hdivisorValue,
      hdivisorNonzero', hdividendSafe, hdivisorSafe,
      hscratch, BitVec.udiv_def]

/- The reduced Loop-to-Word carrier currently uses zero placeholders for the
   handler label and entry section.  The surrounding pipeline supplies the
   concrete function section in the Stack configuration; preserve explicit
   nonzero metadata when it is already available. -/
def wordStackHandlerLabel (config : WordStackConfig) : Nat → Nat
  | 0 => config.handlerLabel
  | label + 1 => label + 1

def wordStackHandlerEntryLabel (config : WordStackConfig) : Nat → Nat
  | 0 => config.sectionId
  | entry + 1 => entry + 1

/-! CakeML's `call_dest NONE args` takes the target of an indirect call from
    the last argument.  `wReg2` leaves a register-resident target in its own
    register and, for a stack-resident target, loads it into the register above
    the ABI window.  The remaining arguments are the callee's formals; the
    target slot is not part of the argument relocation.  This returns the
    direct argument list, the stack-level target, and any target load that must
    run after the argument moves. -/
def wordStackIndirectCallNat (config : WordStackConfig) (arguments : List Nat) :
    Option (List Nat × StackCallTarget × StackProg Nat) :=
  match arguments.getLast? with
  | none => some ([], .label stackRaiseStubLocation, .skip)
  | some target =>
      let direct := arguments.dropLast
      match wordStackLocation config target with
      | some (.register register) => some (direct, .register register, .skip)
      | some (.stack slot) =>
          some (direct, .register config.scratch,
            .stackLoad config.scratch (wordStackOffset config slot))
      | none => none

/-- Cake's `stack_free` count for a call target: the frame size `f` minus the
    number of stack-resident arguments.  A direct call passes its argument
    count; an indirect call passes one fewer because its last argument is the
    target. -/
def wordStackCallFreeCount (config : WordStackConfig) (argumentCount : Nat) : Nat :=
  wordStackCakeFrameSize config - (argumentCount - config.abiRegisterCount)

def wordToStackProg {α : Type} [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Div α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (config : WordStackConfig) : WordProg α → Option (StackProg α)
  | .skip => some .skip
  | .move _ moves => wordStackMoveList config moves
  | .assign destination (.var source) =>
      wordStackMove config destination source
  | .locValue destination source =>
      wordStackLocValue config destination source
  | .inst instruction =>
      wordToStackInst config instruction
  | .get destination store =>
      wordStackGet config destination store
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
  | .mustTerminate body => wordToStackProg config body
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return returnLabel values => wordStackReturn config returnLabel values
  | .call none (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let callCode := .call none (.label target) none
      let freeCount := wordStackCallFreeCount config arguments.length
      pure (wordStackJoin argumentMoves (stackFreeIfNonzero freeCount callCode))
  | .tick => pure .tick
  | .call returns (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let returnCode ← wordStackReturnCode config returns
      let destinations := returns.map (fun result => result.1) |>.getD []
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        config.returnLabel config.entryLabel
      pure (wordStackJoin argumentMoves callCode)
  | .call returns (some target) arguments
      (some (exception, body, handlerLabel, entryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let returnCode ← wordStackReturnCode config returns
      let _destinations := returns.map (fun result => result.1) |>.getD []
      let handlerCode ← wordToStackProg config body
      let callCode := wordToStackCallWithHandlerInSection config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        config.returnLabel config.entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config entryLabel) exception
      pure (wordStackJoin argumentMoves callCode)
  | .opCurrHeap operator destination source =>
      wordStackOpCurrHeap config operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      wordStackInstall config codeBuffer codeLength dataBuffer dataLength
  | .codeBufferWrite address value =>
      wordStackBufferWrite config true address value
  | .dataBufferWrite address value =>
      wordStackBufferWrite config false address value
  | .alloc _ _ | .storeConsts _ _ _ _ _ => none
  | .ffi function configuration configurationLength array arrayLength _ =>
      wordStackFfi config function configuration configurationLength array arrayLength
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
  | .move _ moves => wordStackMoveList config moves
  | .assign destination value => wordStackCompileExpNat config destination value
  | .locValue destination source => wordStackLocValue config destination source
  | .inst instruction => wordToStackInst config instruction
  | .get destination store => wordStackGet config destination store
  | .store address value =>
      match address with
      | .const _ | .var _ | .lookup _ =>
          wordStackCompileStoreNat config address (.var value)
      | _ => wordStackCompileStoreNatNested config address (.var value)
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
  | .mustTerminate body => wordToStackProgNat config body
  | .break label => pure (.break label)
  | .continue label => pure (.continue label)
  | .raise exception => pure (wordToStackRaise exception)
  | .return returnLabel values => wordStackReturn config returnLabel values
  | .call none (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let callCode := .call none (.label target) none
      let freeCount := wordStackCallFreeCount config arguments.length
      pure (wordStackJoin argumentMoves (stackFreeIfNonzero freeCount callCode))
  | .tick => pure .tick
  | .call (some (destinations, _cutsets, returnProgram, returnLabel, entryLabel))
      (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let returnCode ← wordToStackProgNat config returnProgram
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        returnLabel entryLabel
      pure (wordStackJoin argumentMoves callCode)
  | .call none (some target) arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let handlerCode ← wordToStackProgNat config body
      let callCode := wordToStackCallWithHandlerInSection config.perf target arguments.length
        config.frameOffset config.scratch .skip handlerCode
        config.returnLabel config.entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves callCode)
  | .call (some (_destinations, _cutsets, returnProgram, returnLabel, entryLabel))
      (some target) arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let returnCode ← wordToStackProgNat config returnProgram
      let handlerCode ← wordToStackProgNat config body
      let callCode := wordToStackCallWithHandlerInSection config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        returnLabel entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves callCode)
  | .call none none arguments none => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let callCode := .call none target none
      let freeCount := wordStackCallFreeCount config (arguments.length - 1)
      pure (wordStackJoin argumentMoves
        (wordStackJoin targetLoad (stackFreeIfNonzero freeCount callCode)))
  | .call none none arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let handlerCode ← wordToStackProgNat config body
      let callCode := wordToStackCallWithHandlerInSectionTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch .skip handlerCode
        config.returnLabel config.entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves (wordStackJoin targetLoad callCode))
  | .call (some (_destinations, _cutsets, returnProgram, returnLabel, entryLabel))
      none arguments none => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let returnCode ← wordToStackProgNat config returnProgram
      let callCode := wordToStackCallNoHandlerTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch _destinations returnCode
        returnLabel entryLabel
      pure (wordStackJoin argumentMoves (wordStackJoin targetLoad callCode))
  | .call (some (_destinations, _cutsets, returnProgram, returnLabel, entryLabel))
      none arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let returnCode ← wordToStackProgNat config returnProgram
      let handlerCode ← wordToStackProgNat config body
      let callCode := wordToStackCallWithHandlerInSectionTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch returnCode handlerCode
        returnLabel entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves (wordStackJoin targetLoad callCode))
  | .opCurrHeap operator destination source =>
      wordStackOpCurrHeap config operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      wordStackInstall config codeBuffer codeLength dataBuffer dataLength
  | .codeBufferWrite address value =>
      wordStackBufferWrite config true address value
  | .dataBufferWrite address value =>
      wordStackBufferWrite config false address value
  | .alloc _ _ | .storeConsts _ _ _ _ _ => none
  | .ffi function configuration configurationLength array arrayLength _ =>
      wordStackFfi config function configuration configurationLength array arrayLength
  | .shareInst operator name address =>
      wordStackCompileSharedNat config operator name address
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/- Compile the continuation carried in a Word call's return metadata.  The
   older `wordStackReturnCode` helper only reconstructs the ABI destination
   move for reduced fixtures; this boundary retains the actual SSA-generated
   continuation so the complete call lowering can consume it. -/
def wordStackEmbeddedReturnCode [BEq Nat] (config : WordStackConfig)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat)) :
    Option (StackProg Nat) :=
  match returns with
  | none => some .skip
  | some (_, _, returnProgram, _, _) => wordToStackProgNat config returnProgram

/-! The Cake full-SSA pass prefixes the renamed body with an entry move, then
    `remove_dead_prog` can delete formals which are never read.  The frame
    reservation still uses the complete formal count, but the physical entry
    moves must use only the surviving destinations; otherwise dead formals can
    be allocated to the same register and make `parmove` reject the list. -/
def wordStackLiveEntryParameters (program : WordProg (Word width)) : List Nat :=
  match program with
  | .seq (.move _ moves) _ => moves.map Prod.fst
  | _ => []

def wordStackLiveEntryMoves (program : WordProg (Word width)) : List (Nat × Nat) :=
  match program with
  | .seq (.move _ moves) _ => moves
  | _ => []

def wordStackReturnLabel (config : WordStackConfig)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat)) : Nat :=
  returns.map (fun result => result.2.2.2.fst) |>.getD config.returnLabel

def wordStackEntryLabel (config : WordStackConfig)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat)) : Nat :=
  returns.map (fun result => result.2.2.2.snd) |>.getD config.entryLabel

/-! CakeML's `comp` emits the live bitmap for a returning call before it
    compiles the return continuation.  The live set is the GCed component of
    the call cut-set (`wLive_def` passes `SND live` to `write_bitmap`);
    keeping this as a separate state transition makes the order explicit for
    the stateful compiler below. -/
def wordStackCallLiveBitmap [BEq Nat]
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (bitmapRegister frameSlots : Nat)
    (state : WordStackBitmapState)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat)) :
    StackProg Nat × WordStackBitmapState :=
  match returns with
  | none => (.skip, state)
  | some (_, (_, live), _, _, _) =>
      wordStackBitmapWriteWithBuilder config bitmapRegister frameSlots state live
        bitmapBuilder

/-! Stateful variant of the Word-to-Stack compiler.

    The ordinary compiler above intentionally has no bitmap accumulator and
    therefore leaves Alloc and StoreConsts unavailable.  This variant
    follows CakeML's comp state threading for those constructors, structured
    sequencing, and handler bodies.  Other leaves use the existing lowering
    above. -/
def wordToStackProgNatWithBitmapBuilder [BEq Nat]
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState)
  | .seq first second => do
      let (first, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state first
      let (second, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state second
      pure (.seq first second, state)
  | .ite operator condition right thenBranch elseBranch => do
      let (prelude, condition, right) ←
        wordStackConditionOperands config condition right
      let (thenBranch, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state thenBranch
      let (elseBranch, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state elseBranch
      pure (wordStackJoin prelude
        (.ite operator condition right thenBranch elseBranch), state)
  | .loop _liveIn body _liveOut => do
      let (body, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state body
      pure (.loop body, state)
  | .mustTerminate body =>
      wordToStackProgNatWithBitmapBuilder config bitmapBuilder registerCount bitmapRegister frameSlots
        wordBits storeConstsStub state body
  | .assign destination value =>
      (wordStackCompileExpToPhysicalNat config destination value).map
        (fun program => (program, state))
  | .call returns (some target) arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmap config bitmapBuilder
        bitmapRegister frameSlots state returns
      let (returnCode, state) ←
        match returns with
        | some (_, _, returnProgram, _, _) =>
            wordToStackProgNatWithBitmapBuilder config bitmapBuilder
              registerCount bitmapRegister frameSlots wordBits storeConstsStub state
              returnProgram
        | none => pure (.skip, state)
      let (handlerCode, state) ← wordToStackProgNatWithBitmapBuilder config
        bitmapBuilder registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandlerInSection config.perf target arguments.length
        config.frameOffset config.scratch returnCode handlerCode
        (wordStackReturnLabel config returns) (wordStackEntryLabel config returns)
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves (wordStackJoin liveCode callCode), state)
  | .call (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmap config bitmapBuilder
        bitmapRegister frameSlots state
        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      let (returnCode, state) ← wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state returnProgram
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode
        returnLabel entryLabel
      pure (wordStackJoin argumentMoves (wordStackJoin liveCode callCode), state)
  | .alloc _ (_, live) =>
      let (program, state) := wordStackAllocWithBitmapBuilder config bitmapRegister
        frameSlots state live bitmapBuilder
      pure (program, state)
  | .storeConsts _ _ _ _ constants =>
      let (program, state) := wordStackStoreConstsWithBitmaps config registerCount
        config.specialScratch wordBits storeConstsStub state constants
      pure (program, state)
  | program =>
      (wordToStackProgNat config program).map (fun program => (program, state))
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordToStackProgNatWithBitmaps [BEq Nat]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithBitmapBuilder config
    (wordStackLiveBitmap registerCount frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state

theorem wordStackBitmapState_insert_length
    (state : WordStackBitmapState) (bitmap : List Nat)
    (hstate : state.length = state.data.length) :
    (wordStackInsertBitmap state bitmap).1.length =
      (wordStackInsertBitmap state bitmap).1.data.length := by
  simp [wordStackInsertBitmap, hstate]

theorem wordStackBitmapState_alloc_length
    (config : WordStackConfig) (bitmapRegister frameSlots : Nat)
    (state : WordStackBitmapState) (live : List Nat)
    (bitmapBuilder : List Nat → List Nat)
    (hstate : state.length = state.data.length) :
    (wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state
      live bitmapBuilder).2.length =
      (wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots state
        live bitmapBuilder).2.data.length := by
  by_cases hframes : frameSlots = 0
  · simp [wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      hframes, hstate]
  · simp [wordStackAllocWithBitmapBuilder, wordStackBitmapWriteWithBuilder,
      wordStackInsertBitmap, hframes, hstate]

theorem wordStackBitmapState_storeConsts_length
    (config : WordStackConfig) (registerCount specialScratch wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (constants : List (Bool × Nat))
    (hstate : state.length = state.data.length) :
    (wordStackStoreConstsWithBitmaps config registerCount specialScratch wordBits
      storeConstsStub state constants).2.length =
      (wordStackStoreConstsWithBitmaps config registerCount specialScratch wordBits
        storeConstsStub state constants).2.data.length := by
  simp [wordStackStoreConstsWithBitmaps, wordStackInsertBitmap, hstate]

theorem wordStackCallLiveBitmap_length
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (returns : Option (List Nat × (List Nat × List Nat) × WordProg Nat × Nat × Nat))
    (hstate : state.length = state.data.length) :
    (wordStackCallLiveBitmap config bitmapBuilder bitmapRegister frameSlots state
      returns).2.length =
      (wordStackCallLiveBitmap config bitmapBuilder bitmapRegister frameSlots state
        returns).2.data.length := by
  cases returns with
  | none => exact hstate
  | some returnData =>
      rcases returnData with ⟨destinations, cutsets, returnProgram, returnLabel,
        entryLabel⟩
      by_cases hframes : frameSlots = 0
      · simp [wordStackCallLiveBitmap, wordStackBitmapWriteWithBuilder, hframes,
          hstate]
      · simp [wordStackCallLiveBitmap, wordStackBitmapWriteWithBuilder,
          wordStackInsertBitmap, hframes, hstate]

theorem wordToStackProgNatWithBitmapBuilder_preserves_length
    [BEq Nat] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg Nat)
    (hstate : state.length = state.data.length)
    (compiled : StackProg Nat) (finalState : WordStackBitmapState)
    (hresult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
      registerCount bitmapRegister frameSlots wordBits storeConstsStub state program =
      some (compiled, finalState)) :
    finalState.length = finalState.data.length := by
  cases program <;> try simp [wordToStackProgNatWithBitmapBuilder, Option.bind] at hresult
  all_goals try
    (rcases hresult with ⟨_, _, rfl, rfl⟩
      <;> exact hstate)
  case seq first second =>
      generalize hfirstResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state first =
        firstResult at hresult
      cases firstResult with
      | none => simp_all
      | some firstPair =>
          cases firstPair with
          | mk firstCode firstState =>
              have hfirst : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                  registerCount bitmapRegister frameSlots wordBits storeConstsStub state first =
                  some (firstCode, firstState) := hfirstResult
              simp [] at hresult
              generalize hsecondResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                registerCount bitmapRegister frameSlots wordBits storeConstsStub firstState second =
                secondResult at hresult
              cases secondResult with
              | none => simp_all
              | some secondPair =>
                  cases secondPair with
                  | mk secondCode secondFinalState =>
                      have hsecond : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                          registerCount bitmapRegister frameSlots wordBits storeConstsStub firstState second =
                          some (secondCode, secondFinalState) := hsecondResult
                      simp [] at hresult
                      have hfirstState := wordToStackProgNatWithBitmapBuilder_preserves_length
                        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                        storeConstsStub state first hstate firstCode firstState hfirst
                      have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                        storeConstsStub firstState second hfirstState secondCode
                        secondFinalState hsecond
                      rcases hresult with ⟨_, rfl⟩
                      exact hfinal
  case ite operator condition right thenBranch elseBranch =>
      generalize hconditionResult : wordStackConditionOperands config condition right =
        conditionResult at hresult
      cases conditionResult with
      | none => simp_all
      | some conditionPair =>
          cases conditionPair with
          | mk conditionPrelude conditionRest =>
              cases conditionRest with
              | mk conditionRegister rightOperand =>
                  simp [] at hresult
                  generalize hthenResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                    registerCount bitmapRegister frameSlots wordBits storeConstsStub state thenBranch =
                    thenResult at hresult
                  cases thenResult with
                  | none => simp_all
                  | some thenPair =>
                      cases thenPair with
                      | mk thenCode thenState =>
                          simp [] at hresult
                          generalize helseResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
                            registerCount bitmapRegister frameSlots wordBits storeConstsStub thenState elseBranch =
                            elseResult at hresult
                          cases elseResult with
                          | none => simp_all
                          | some elsePair =>
                              cases elsePair with
                              | mk elseCode finalResult =>
                                  have hthenState := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub state thenBranch hstate thenCode thenState hthenResult
                                  have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub thenState elseBranch hthenState elseCode finalResult
                                    helseResult
                                  rcases hresult with ⟨_, rfl⟩
                                  exact hfinal
  case loop liveIn body liveOut =>
      generalize hbodyResult : wordToStackProgNatWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body =
        bodyResult at hresult
      cases bodyResult with
      | none => simp_all
      | some bodyPair =>
          cases bodyPair with
          | mk bodyCode finalResult =>
              have hfinal := wordToStackProgNatWithBitmapBuilder_preserves_length
                config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                storeConstsStub state body hstate bodyCode finalResult hbodyResult
              rcases hresult with ⟨_, rfl⟩
              exact hfinal
  case mustTerminate body =>
      exact wordToStackProgNatWithBitmapBuilder_preserves_length
        config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
        storeConstsStub state body hstate compiled finalState hresult
  case call returns target arguments handler =>
      cases target with
      | none =>
          simp [wordToStackProgNatWithBitmapBuilder] at hresult
          rcases hresult with ⟨_, _, rfl, rfl⟩
          exact hstate
      | some target =>
          cases handler with
          | none =>
              cases returns with
              | none =>
                  simp [wordToStackProgNatWithBitmapBuilder] at hresult
                  rcases hresult with ⟨_, _, rfl, rfl⟩
                  exact hstate
              | some returnData =>
                  rcases returnData with
                    ⟨destinations, cutsets, returnProgram, returnLabel, entryLabel⟩
                  simp only [wordToStackProgNatWithBitmapBuilder] at hresult
                  cases hargs : wordStackMovesToPhysical config arguments config.abiBase with
                  | none =>
                      rw [hargs] at hresult
                      simp at hresult
                  | some argumentMoves =>
                      cases hlive : wordStackCallLiveBitmap config bitmapBuilder
                        bitmapRegister frameSlots state
                        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel)) with
                      | mk liveCode liveState =>
                          simp [hargs, hlive] at hresult
                          cases hreturn : wordToStackProgNatWithBitmapBuilder
                            config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                            storeConstsStub liveState returnProgram with
                          | none =>
                              rw [hreturn] at hresult
                              simp at hresult
                          | some returnPair =>
                              cases returnPair with
                              | mk returnCode finalState =>
                                  have hliveInv : liveState.length = liveState.data.length := by
                                    have hlive0 := wordStackCallLiveBitmap_length config bitmapBuilder
                                      bitmapRegister frameSlots state
                                      (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
                                      hstate
                                    have hliveState : (wordStackCallLiveBitmap config bitmapBuilder
                                      bitmapRegister frameSlots state
                                      (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))).snd =
                                      liveState := by
                                      simpa using congrArg Prod.snd hlive
                                    rw [← hliveState]
                                    exact hlive0
                                  have hreturnInv := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub liveState returnProgram hliveInv returnCode finalState
                                    hreturn
                                  simp [hreturn] at hresult
                                  rcases hresult with ⟨_, rfl, rfl⟩
                                  exact hreturnInv
          | some handlerData =>
              rcases handlerData with ⟨exception, body, handlerLabel, entryLabel⟩
              simp only [wordToStackProgNatWithBitmapBuilder] at hresult
              cases hargs : wordStackMovesToPhysical config arguments config.abiBase with
              | none =>
                  rw [hargs] at hresult
                  simp at hresult
              | some argumentMoves =>
                  cases returns with
                  | none =>
                      cases hlive : wordStackCallLiveBitmap config bitmapBuilder
                        bitmapRegister frameSlots state none with
                      | mk liveCode liveState =>
                          simp [hargs, hlive] at hresult
                          cases hhandler : wordToStackProgNatWithBitmapBuilder
                            config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                            storeConstsStub liveState body with
                          | none =>
                              rw [hhandler] at hresult
                              simp at hresult
                          | some handlerPair =>
                              cases handlerPair with
                              | mk handlerCode finalResult =>
                                  have hliveInv : liveState.length = liveState.data.length := by
                                    have hlive0 := wordStackCallLiveBitmap_length config bitmapBuilder
                                      bitmapRegister frameSlots state none hstate
                                    have hliveState : (wordStackCallLiveBitmap config bitmapBuilder
                                      bitmapRegister frameSlots state none).snd = liveState := by
                                      simpa using congrArg Prod.snd hlive
                                    rw [← hliveState]
                                    exact hlive0
                                  have hhandlerInv := wordToStackProgNatWithBitmapBuilder_preserves_length
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub liveState body hliveInv handlerCode finalResult
                                    hhandler
                                  simp [hhandler] at hresult
                                  rcases hresult with ⟨_, rfl, rfl⟩
                                  exact hhandlerInv
                  | some returnData =>
                      rcases returnData with
                        ⟨destinations, cutsets, returnProgram, returnLabel, entryLabel⟩
                      cases hlive : wordStackCallLiveBitmap config bitmapBuilder
                        bitmapRegister frameSlots state
                        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel)) with
                      | mk liveCode liveState =>
                          simp [hargs, hlive] at hresult
                          cases hreturn : wordToStackProgNatWithBitmapBuilder
                            config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                            storeConstsStub liveState returnProgram with
                          | none =>
                              rw [hreturn] at hresult
                              simp at hresult
                          | some returnPair =>
                              cases returnPair with
                              | mk returnCode returnState =>
                                  simp [hreturn] at hresult
                                  cases hhandler : wordToStackProgNatWithBitmapBuilder
                                    config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                    storeConstsStub returnState body with
                                  | none =>
                                      rw [hhandler] at hresult
                                      simp at hresult
                                  | some handlerPair =>
                                      cases handlerPair with
                                      | mk handlerCode finalResult =>
                                          have hliveInv : liveState.length = liveState.data.length := by
                                            have hlive0 := wordStackCallLiveBitmap_length config bitmapBuilder
                                              bitmapRegister frameSlots state
                                              (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
                                              hstate
                                            have hliveState : (wordStackCallLiveBitmap config bitmapBuilder
                                              bitmapRegister frameSlots state
                                              (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))).snd =
                                              liveState := by
                                              simpa using congrArg Prod.snd hlive
                                            rw [← hliveState]
                                            exact hlive0
                                          have hreturnInv := wordToStackProgNatWithBitmapBuilder_preserves_length
                                            config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                            storeConstsStub liveState returnProgram hliveInv returnCode returnState
                                            hreturn
                                          have hhandlerInv := wordToStackProgNatWithBitmapBuilder_preserves_length
                                            config bitmapBuilder registerCount bitmapRegister frameSlots wordBits
                                            storeConstsStub returnState body hreturnInv handlerCode finalResult
                                            hhandler
                                          simp [hhandler] at hresult
                                          rcases hresult with ⟨_, rfl, rfl⟩
                                          exact hhandlerInv
  case alloc destination cutsets =>
      rw [wordToStackProgNatWithBitmapBuilder] at hresult
      generalize hallocResult : wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots
        state cutsets.2 bitmapBuilder = allocResult at hresult
      cases allocResult with
      | mk allocCode allocState =>
          rcases hresult with ⟨_, rfl⟩
          have hallocState := congrArg Prod.snd hallocResult
          have hallocState' : (wordStackAllocWithBitmapBuilder config bitmapRegister
              frameSlots state cutsets.2 bitmapBuilder).2 = finalState := by
            simpa using hallocState
          rw [← hallocState']
          exact wordStackBitmapState_alloc_length config bitmapRegister frameSlots state
            cutsets.2 bitmapBuilder hstate
  case storeConsts source bitmap codeLength dataLength constants =>
      rw [← hresult.2]
      exact wordStackBitmapState_storeConsts_length config registerCount
        config.specialScratch wordBits storeConstsStub state constants hstate
def wordToStackProgNatWithLocationBitmaps [BEq Nat]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg Nat → Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithBitmapBuilder config
    (wordStackLiveBitmapFromLocations config frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state

/-! The real Word pipeline is indexed by a fixed-width bit-vector type, while
    StackProg keeps constants as natural numbers so that StackRemove can
    materialize them at the target width.  This adapter makes that boundary
    explicit: converting a Word constant to `toNat` is recovered by the
    subsequent `BitVec.ofNat` performed by the StackLang machine and LabLang
    backend. -/

def wordStoreToNat : WordStore (Word width) → WordStore Nat
  | .temp address => .temp address.toNat
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .currHeap => .currHeap
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd

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

def wordArithToNat : WordArith (Word width) → WordArith Nat
  | .longMul a b c d => .longMul a b c d
  | .longDiv a b c d e => .longDiv a b c d e
  | .addCarry a b c d e => .addCarry a b c d e
  | .cakeAddCarry a b c d => .cakeAddCarry a b c d
  | .div a b c => .div a b c
  | .binOp operator destination sourceLeft sourceRight =>
      .binOp operator destination sourceLeft (wordRegImmToNat sourceRight)
  | .shift operator destination sourceLeft sourceRight =>
      .shift operator destination sourceLeft (wordRegImmToNat sourceRight)

def wordInstToNat : WordInst (Word width) → WordInst Nat
  | .const destination value => .const destination value.toNat
  | .arith operation => .arith (wordArithToNat operation)
  | .mem operator destination address => .mem operator destination address

/- SSA-generated calls carry their complete return continuation and, when
   present, their exception handler as nested Word programs.  Preserve both
   programs at this representation boundary; replacing them with `skip`
   would make the generated call return without restoring the caller state or
   running its continuation. -/
def wordProgToNat : WordProg (Word width) → WordProg Nat
  | .skip => .skip
  | .move priority moves => .move priority moves
  | .assign name value => .assign name (wordExpToNat value)
  | .inst instruction => .inst (wordInstToNat instruction)
  | .get destination store => .get destination (wordStoreToNat store)
  | .store address value => .store (wordExpToNat address) value
  | .set store value => .set (wordStoreToNat store) (wordExpToNat value)
  | .seq first second => .seq (wordProgToNat first) (wordProgToNat second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition (wordRegImmToNat right)
        (wordProgToNat thenBranch) (wordProgToNat elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordProgToNat body) liveOut
  | .mustTerminate body => .mustTerminate (wordProgToNat body)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return label values => .return label values
  | .tick => .tick
  | .locValue destination source => .locValue destination source
  | .call none target arguments none =>
      .call none target arguments none
  | .call (some (values, cutsets, returnCode, returnLabel, entryLabel)) target
      arguments none =>
      .call (some (values, cutsets, wordProgToNat returnCode, returnLabel, entryLabel))
        target arguments none
  | .call none target arguments
      (some (exception, body, handlerLabel, entryLabel)) =>
      .call none target arguments
        (some (exception, wordProgToNat body, handlerLabel, entryLabel))
  | .call (some (values, cutsets, returnCode, returnLabel, entryLabel)) target
      arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call (some (values, cutsets, wordProgToNat returnCode, returnLabel, entryLabel))
        target arguments
          (some (exception, wordProgToNat body, handlerLabel, handlerEntryLabel))
  | .alloc destination (nonGc, gc) =>
      .alloc destination (nonGc, gc)
  | .storeConsts source bitmap codeLength dataLength constants =>
      .storeConsts source bitmap codeLength dataLength
        (constants.map (fun (isByte, value) => (isByte, value.toNat)))
  | .opCurrHeap operator destination source =>
      .opCurrHeap operator destination source
  | .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc) =>
      .install codeBuffer codeLength dataBuffer dataLength (nonGc, gc)
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function configuration configurationLength array arrayLength live
  | .shareInst operator name address =>
      .shareInst operator name (wordExpToNat address)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | (simp [sizeOf] <;> omega)

/-! Fused word-to-stack lowering.  Cake's `compile_prog` lowers the
    word-typed program directly; it does not first rebuild a complete
    `WordProg Nat`.  Keep that shape here as well: expressions and stores are
    converted only at the leaf that consumes them, while nested call
    continuations and handlers are lowered recursively.  The existing
    `wordProgToNat` adapter remains the reference representation for proofs
    and small parity tests. -/

def wordStackCallLiveBitmapWord [BEq Nat]
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (bitmapRegister frameSlots : Nat) (state : WordStackBitmapState)
    (returns : Option (List Nat × (List Nat × List Nat) ×
      WordProg (Word width) × Nat × Nat)) :
    StackProg Nat × WordStackBitmapState :=
  match returns with
  | none => (.skip, state)
  | some (_, (_, live), _, _, _) =>
      wordStackBitmapWriteWithBuilder config bitmapRegister frameSlots state live
        bitmapBuilder

def wordToStackProgWordWithBitmapBuilder [BEq Nat] [NeZero width]
    (config : WordStackConfig) (bitmapBuilder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    WordProg (Word width) → Option (StackProg Nat × WordStackBitmapState)
  | .skip => some (.skip, state)
  | .move _ moves => (wordStackMoveList config moves).map (fun code => (code, state))
  | .assign destination value =>
      (wordStackCompileExpToPhysicalNat config destination (wordExpToNat value)).map
        (fun code => (code, state))
  | .inst (.arith (.binOp operator destination sourceLeft sourceRight)) =>
      /- The register-operand carrier lowers exactly like the expression
         assignment it replaces, so the emitted stack program is unchanged.
         A register immediate keeps the constant in the expression so the
         stack-to-Lab fusion still emits the architectural immediate. -/
      (wordStackCompileExpToPhysicalNat config destination
        (match wordRegImmToNat sourceRight with
         | .reg register => (.op operator [.var sourceLeft, .var register] : WordExp Nat)
         | .imm value => (.op operator [.var sourceLeft, .const value] : WordExp Nat))).map
        (fun code => (code, state))
  | .inst instruction =>
      (wordToStackInst config (wordInstToNat instruction)).map (fun code => (code, state))
  | .get destination store =>
      (wordStackGet config destination (wordStoreToNat store)).map (fun code => (code, state))
  | .store address value =>
      (match address with
      | .const _ | .var _ | .lookup _ =>
          wordStackCompileStoreNat config (wordExpToNat address) (.var value)
      | _ => wordStackCompileStoreNatNested config (wordExpToNat address) (.var value)).map
        (fun code => (code, state))
  | .set store value =>
      (wordStackSetNat config (wordStoreToNat store) (wordExpToNat value)).map
        (fun code => (code, state))
  | .seq first second =>
      let peephole : Option (StackProg Nat × WordStackBitmapState) :=
        match first, second with
        | .move 0 [(destination, source)],
            .seq (.assign name (.op operator [.var left, .const value])) rest =>
            if name = destination && left = destination then
              /- Two-register compensation reads its own destination.  Cake
                 keeps the operand in the temporary that `inst_select` moved
                 it into, so the instruction reads that register while
                 writing the destination (`Binop op tar temp (Imm w)`).
                 Re-reading the move's source keeps that operand register and
                 lets the constant fuse into the immediate instead of copying
                 into the destination first. -/
              match wordStackCompileExpToPhysicalNat config destination
                  (wordExpToNat (.op operator [.var source, .const value])) with
              | none => none
              | some immediateCode => do
                  let (restCode, state) ← wordToStackProgWordWithBitmapBuilder
                    config bitmapBuilder registerCount bitmapRegister frameSlots
                    wordBits storeConstsStub state rest
                  pure (.seq immediateCode restCode, state)
            else
              none
        | _, _ => none
      match peephole with
      | some result => some result
      | none => do
        let (firstCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
          registerCount bitmapRegister frameSlots wordBits storeConstsStub state first
        let (secondCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
          registerCount bitmapRegister frameSlots wordBits storeConstsStub state second
        pure (.seq firstCode secondCode, state)
  | .ite operator condition right thenBranch elseBranch => do
      let right := wordRegImmToNat right
      let (prelude, condition, right) ← wordStackConditionOperands config condition right
      let (thenCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state thenBranch
      let (elseCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state elseBranch
      pure (wordStackJoin prelude (.ite operator condition right thenCode elseCode), state)
  | .loop _ body _ => do
      let (bodyCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      pure (.loop bodyCode, state)
  | .mustTerminate body =>
      wordToStackProgWordWithBitmapBuilder config bitmapBuilder registerCount bitmapRegister
        frameSlots wordBits storeConstsStub state body
  | .break label => some (.break label, state)
  | .continue label => some (.continue label, state)
  | .raise exception => some (wordToStackRaise exception, state)
  | .return returnLabel values =>
      (wordStackReturn config returnLabel values).map (fun code => (code, state))
  | .tick => some (.tick, state)
  | .locValue destination source =>
      (wordStackLocValue config destination source).map (fun code => (code, state))
  | .call (some (destinations, cutsets, returnProgram, returnLabel, entryLabel)) (some target) arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      /- Returning calls carry only value arguments.  The source-shaped
         `loop_to_word$comp` adds the link slot only to tail calls
         (`loop_to_wordScript.sml:131`); ordinary calls therefore begin at
         the value ABI base. -/
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmapWord config bitmapBuilder
        bitmapRegister frameSlots state
        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      let (returnCode, state) ←
        wordToStackProgWordWithBitmapBuilder config bitmapBuilder
          registerCount bitmapRegister frameSlots wordBits storeConstsStub state returnProgram
      let (handlerCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandlerInSectionAtRegisterCount config.perf target
        arguments.length registerCount config.frameOffset config.scratch returnCode handlerCode
        returnLabel entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves (wordStackJoin liveCode callCode), state)
  | .call (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmapWord config bitmapBuilder
        bitmapRegister frameSlots state
        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      let (returnCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state returnProgram
      let callCode := wordToStackCallNoHandler config.perf target arguments.length
        config.frameOffset config.scratch destinations returnCode returnLabel entryLabel
      pure (wordStackJoin argumentMoves (wordStackJoin liveCode callCode), state)
  | .call none (some target) arguments none => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.callAbiBase
      let callCode := .call none (.label target) none
      let freeCount := wordStackCallFreeCount config arguments.length
      pure (wordStackJoin argumentMoves (stackFreeIfNonzero freeCount callCode), state)
  | .call none (some target) arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let argumentMoves ← wordStackMovesToPhysical config arguments config.callAbiBase
      let (handlerCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandlerInSection config.perf target arguments.length
        config.frameOffset config.scratch .skip handlerCode
        config.returnLabel config.entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves callCode, state)
  | .call none none arguments none => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let callCode := .call none target none
      let freeCount := wordStackCallFreeCount config (arguments.length - 1)
      pure (wordStackJoin argumentMoves
        (wordStackJoin targetLoad (stackFreeIfNonzero freeCount callCode)), state)
  | .call none none arguments
      (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let (handlerCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandlerInSectionTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch .skip handlerCode
        config.returnLabel config.entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves (wordStackJoin targetLoad callCode), state)
  | .call (some (destinations, cutsets, returnProgram, returnLabel, entryLabel)) none
      arguments none => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmapWord config bitmapBuilder
        bitmapRegister frameSlots state
        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      let (returnCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state returnProgram
      let callCode := wordToStackCallNoHandlerTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch destinations returnCode
        returnLabel entryLabel
      pure (wordStackJoin argumentMoves
        (wordStackJoin targetLoad (wordStackJoin liveCode callCode)), state)
  | .call (some (destinations, cutsets, returnProgram, returnLabel, entryLabel)) none
      arguments (some (exception, body, handlerLabel, handlerEntryLabel)) => do
      let (direct, target, targetLoad) ← wordStackIndirectCallNat config arguments
      let argumentMoves ← wordStackMovesToPhysical config direct config.abiBase
      let (liveCode, state) := wordStackCallLiveBitmapWord config bitmapBuilder
        bitmapRegister frameSlots state
        (some (destinations, cutsets, returnProgram, returnLabel, entryLabel))
      let (returnCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state returnProgram
      let (handlerCode, state) ← wordToStackProgWordWithBitmapBuilder config bitmapBuilder
        registerCount bitmapRegister frameSlots wordBits storeConstsStub state body
      let callCode := wordToStackCallWithHandlerInSectionTarget config.perf target
        (arguments.length - 1) config.frameOffset config.scratch returnCode handlerCode
        returnLabel entryLabel
        (wordStackHandlerLabel config handlerLabel)
        (wordStackHandlerEntryLabel config handlerEntryLabel) exception
      pure (wordStackJoin argumentMoves
        (wordStackJoin targetLoad (wordStackJoin liveCode callCode)), state)
  | .alloc _ (_, live) =>
      let (code, state) := wordStackAllocWithBitmapBuilder config bitmapRegister frameSlots
        state live bitmapBuilder
      some (code, state)
  | .storeConsts _ _ _ _ constants =>
      let constants := constants.map (fun (isByte, value) => (isByte, value.toNat))
      let (code, state) := wordStackStoreConstsWithBitmaps config registerCount
        config.specialScratch wordBits storeConstsStub state constants
      some (code, state)
  | .opCurrHeap operator destination source =>
      (wordStackOpCurrHeap config operator destination source).map (fun code => (code, state))
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      (wordStackInstall config codeBuffer codeLength dataBuffer dataLength).map
        (fun code => (code, state))
  | .codeBufferWrite address value =>
      (wordStackBufferWrite config true address value).map (fun code => (code, state))
  | .dataBufferWrite address value =>
      (wordStackBufferWrite config false address value).map (fun code => (code, state))
  | .ffi function configuration configurationLength array arrayLength _ =>
      (wordStackFfi config function configuration configurationLength array arrayLength).map
        (fun code => (code, state))
  | .shareInst operator name address =>
      (wordStackCompileSharedNat config operator name (wordExpToNat address)).map
        (fun code => (code, state))
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | (simp [sizeOf] <;> omega)

/-! Cake's full-SSA FFI block is preceded by a `Move1` ABI shuffle.  The
    source allocator's sequence traversal leaves the constant writes in the
    reverse order immediately before that shuffle; preserving this observable
    order is required for byte parity even though the values are independent.
    Restrict the rewrite to the source-shaped pre-FFI pattern and leave the
    ordinary hardware-numbered path untouched. -/
def wordProgSeqItems : WordProg α → List (WordProg α)
  | .seq first second => wordProgSeqItems first ++ wordProgSeqItems second
  | program => [program]

def wordProgSeqBuild : List (WordProg α) → WordProg α
  | [] => .skip
  | program :: programs =>
      programs.foldl (fun current next => .seq current next) program

def wordProgIsFfi : WordProg α → Bool
  | .ffi _ _ _ _ _ _ => true
  | _ => false

def wordProgIsConstAssign : WordProg α → Bool
  | .assign _ (.const _) => true
  | _ => false

def wordProgReverseFfiConstSetup (program : WordProg α) : WordProg α :=
  let items := wordProgSeqItems program
  let (pre, suffix) := items.span (fun item => !wordProgIsFfi item)
  match suffix, pre.reverse with
  | .ffi function configuration configurationLength array arrayLength live :: rest,
      .move priority moves :: beforeMoveRev =>
      let (constantsRev, remainderRev) :=
        beforeMoveRev.span wordProgIsConstAssign
      let reordered := remainderRev.reverse ++ constantsRev ++
        [.move priority moves]
      wordProgSeqBuild (reordered ++
        [.ffi function configuration configurationLength array arrayLength live] ++ rest)
  | _, _ => program

def wordToStackProgWordWithBitmapsFused [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgWordWithBitmapBuilder config
    (wordStackLiveBitmap registerCount frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state program

def wordToStackProgWordWithLocationBitmapsFused [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgWordWithBitmapBuilder config
    (wordStackLiveBitmapFromLocations config frameSlots wordBits)
    registerCount bitmapRegister frameSlots wordBits storeConstsStub state program

def wordToStackProgWord [NeZero width] (config : WordStackConfig)
    (program : WordProg (Word width)) : Option (StackProg Nat) :=
  wordToStackProgNat config (wordProgToNat program)

def wordToStackProgWordWithBitmaps [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
  Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgWordWithBitmapsFused config registerCount bitmapRegister frameSlots width
    storeConstsStub state program

def wordToStackProgWordWithLocationBitmaps [NeZero width]
    (config : WordStackConfig) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
  Option (StackProg Nat × WordStackBitmapState) :=
  wordToStackProgNatWithLocationBitmaps config registerCount bitmapRegister frameSlots width
    storeConstsStub state (wordProgToNat program)

/-! Function-entry lowering for allocated Word programs.  Cake's stack ABI
    places arguments in stack registers beginning at 1; the allocator may
    place a formal parameter in a different register or in a spill slot.  The
    entry moves make that calling convention explicit before the lowered body
    starts executing. -/
def wordToStackFunctionWithParameters [NeZero width]
    (config : WordStackConfig) (_parameters : List Nat)
    (program : WordProg (Word width)) : Option (StackProg Nat) := do
  /- Cake's `word_to_stack.compile_prog` only reserves the frame here: the
     incoming arguments already sit in the fixed Cake ABI registers and the
     SSA entry move (`wordSsaRenameFunctionWithEntry`) copies them into their
     fresh names.  A second parameter prelude double-copies and can collide
     because the allocator may merge a dead entry destination with a live
     one. -/
  wordToStackProgWord config program

def wordToStackFunctionWithParametersAndBitmaps [NeZero width]
    (config : WordStackConfig) (_parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
  Option (StackProg Nat × WordStackBitmapState) := do
  wordToStackProgWordWithBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program

def wordToStackFunctionWithParametersAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (_parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
  Option (StackProg Nat × WordStackBitmapState) := do
  wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program

/-! Cake's `word_to_stack.compile_prog` reserves the maximum spill frame at
    function entry and subtracts the stack-resident argument count from that
    reservation.  Keep this wrapper separate from the historical entrypoint
    so callers that still model an unframed function retain their API. -/
def wordStackFrameWords (parameters : List Nat) (registerCount frameSlots : Nat) : Nat :=
  (if frameSlots = 0 then 0 else frameSlots + 1) - (parameters.length - registerCount)

def wordToStackFunctionWithCakeFrameAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program
  let frameWords := wordStackFrameWords parameters registerCount frameSlots
  pure (wordStackJoin (.stackAlloc frameWords) body, state)

/-! Source-facing full-SSA lowering has already applied Cake's dead-program
    pass.  In that path an absent entry move means that all formal copies were
    removed; keep the complete formal list for frame sizing but emit no dead
    physical entry moves. -/
def wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves
    [NeZero width] (config : WordStackConfig) (_parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program
  pure (body, state)

def wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves
    [NeZero width] (config : WordStackConfig) (parameters : List Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program
  let frameWords := wordStackFrameWords parameters registerCount frameSlots
  pure (wordStackJoin (.stackAlloc frameWords) body, state)

/-! Source-shaped entry lowering with an explicit target ABI source map.  This
    is the same Cake frame and bitmap lowering as the ordinary entrypoint, but
    it preserves special source names such as Word slot 0 -> RISC-V link
    register instead of assuming a single consecutive source-register base. -/
def wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources
    [NeZero width] (config : WordStackConfig) (_parameters : List Nat)
    (_sourceRegister : Nat → Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program
  pure (body, state)

def wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources
    [NeZero width] (config : WordStackConfig) (parameters : List Nat)
    (_sourceRegister : Nat → Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) := do
  let (body, state) ← wordToStackProgWordWithLocationBitmapsFused config registerCount
    bitmapRegister frameSlots width storeConstsStub state program
  let frameWords := wordStackFrameWords parameters registerCount frameSlots
  pure (wordStackJoin (.stackAlloc frameWords) body, state)

/-! Public entry point for the spill-aware path.  The allocator's location
    map is authoritative for the renamed Word program; the remaining stack
    and bitmap configuration stays with the caller because it depends on the
    enclosing frame and linked runtime sections. -/
def wordToStackFunctionWithSpillStateAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (_parameters : List Nat)
    (allocation : WordSpillState)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
  Option (StackProg Nat × WordStackBitmapState) :=
  /- This entrypoint is retained as the reference adapter for the existing
     allocator correctness contracts.  Executable pipeline callers use the
     fused location-aware entrypoints above; keeping this boundary on the
     explicit `wordProgToNat` path lets those contracts continue to expose
     the original Cake-shaped intermediate program. -/
  wordToStackProgWordWithLocationBitmaps
    { config with locations := allocation.locations }
    registerCount bitmapRegister frameSlots storeConstsStub state program

/-! Graph allocation produces the source-to-location map from the renamed
    program's graph colours.  This adapter keeps the renamed names intact and
    feeds that map directly to the location-aware StackLang lowering. -/
def wordToStackFunctionWithGraphAllocationAndLocationBitmaps [NeZero width]
    (config : WordStackConfig) (_parameters : List Nat)
    (allocation : WordGraphAllocation) (colours stackStart : Nat)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (program : WordProg (Word width)) :
    Option (StackProg Nat × WordStackBitmapState) :=
  /- Keep the graph-allocation bridge on the explicit reference adapter for
     the graph correctness contracts.  The executable source pipeline uses
     the fused parameter/frame entrypoints above. -/
  wordToStackProgWordWithLocationBitmaps
    { config with locations := wordGraphLocations allocation colours stackStart }
    registerCount bitmapRegister frameSlots storeConstsStub state program

/-! Compose CakeML-shaped SSA/graph allocation with the actual location-aware
    StackLang entry point.  The allocation witness and renamed metadata are
    retained in the result so later linking and correctness layers can use
    the same graph proof that justified the locations. -/
/-! Compose the ABI-correct full-SSA spill allocator with the location-aware
    Word-to-Stack entry point.  This is the public bridge used before the
    frame-machine proof consumes the generated program. -/
def wordAllocateSsaFunctionWithEntryAndSpillToStack [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    Option (WordSsaState × List Nat × WordProg (Word width) ×
      WordSpillState × StackProg Nat × WordStackBitmapState) := do
  let (ssaState, renamedParameters, renamedProgram, allocation) ←
    wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
      parameters program
  let (stackProgram, finalState) ←
    wordToStackFunctionWithSpillStateAndLocationBitmaps config
      renamedParameters allocation registerCount bitmapRegister frameSlots
      storeConstsStub state renamedProgram
  pure (ssaState, renamedParameters, renamedProgram, allocation,
    stackProgram, finalState)

def wordAllocateGraphFunctionWithStackOnlyToStack [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (fixedSources : List Nat)
    (colours stackStart : Nat) (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) :
    Option (WordSsaState × List Nat × WordGraphAllocation ×
      StackProg Nat × WordStackBitmapState) := do
  let (ssaState, renamedParameters, allocation, renamedProgram) ←
    wordAllocateGraphFunctionWithStackOnlyRenamed parameters program fixedSources
      colours stackStart
  let (stackProgram, state) ←
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps config
      renamedParameters allocation colours stackStart registerCount bitmapRegister
      frameSlots storeConstsStub state renamedProgram
  pure (ssaState, renamedParameters, allocation, stackProgram, state)

/-! Location map used by the currently register-coloured pipeline fragment.
    The spill-aware entry point above accepts the allocator-produced map
    directly; this identity helper remains useful for the register-only path.
-/
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
      some (.stackStore 5 12 : StackProg Nat) := by
  simp [wordStackMove, wordStackLocation, wordStackOffset, lookupNatInfo]

theorem wordStackMove_spill_to_register :
    wordStackMove
        { locations := [(0, .register 4), (1, .stack 2)],
          scratch := 31, stackBase := 10 } 0 1 =
      some (.stackLoad 4 12 : StackProg Nat) := by
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
