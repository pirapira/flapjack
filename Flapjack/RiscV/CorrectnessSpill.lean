import Flapjack.RiscV.CorrectnessWordToStack

/-!
# Spill-aware Word-to-Stack state contracts

The single-destination move theorem establishes the value at the destination,
but a compiler simulation also needs the frame relation for every unrelated
variable.  This file adds that preservation contract with the two necessary
side conditions: the unrelated location is not the move destination and is
not the scratch register used by stack moves.
-/

namespace Flapjack.RiscV

/-! A location-indexed observation of the values represented by a Word-to-Stack
    state.  The relation is intentionally one-way: later compiler passes may
    carry additional machine data that is not part of the source value map. -/
def wordStackMappedValues [NeZero width] (config : WordStackConfig)
    (values : Nat → Option (Word width))
    (state : WordStackMachineState width) : Prop :=
  ∀ name value location,
    values name = some value →
    wordStackLocation config name = some location →
    wordStackMachineValue config state name = some value

def wordStackMappedValuesExcept [NeZero width] (config : WordStackConfig)
    (destination : Nat) (values : Nat → Option (Word width))
    (state : WordStackMachineState width) : Prop :=
  ∀ name value location,
    name ≠ destination →
    values name = some value →
    wordStackLocation config name = some location →
    wordStackMachineValue config state name = some value

/-! The location-indexed form is the natural intermediate relation for the
    parallel move algorithm.  Unlike `wordStackMachineValue`, it does not
    perform a name lookup: its input is already the physical location selected
    by the allocator. -/
def wordStackLocationValue [NeZero width] (config : WordStackConfig)
    (state : WordStackMachineState width) : WordLocation → Word width
  | .register register => state.registers register
  | .stack slot => state.stack (wordStackOffset config slot)

theorem evalWordStackMachine_locationMove_preserves_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : WordLocation)
    (heval : (wordStackLocationMove config destination source).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final destination =
      wordStackLocationValue config state source := by
  cases destination with
  | register destination =>
      cases source with
      | register source =>
          by_cases hsame : destination = source
          · simp [wordStackLocationMove, hsame] at heval
            cases heval
            subst source
            rfl
          · simp [wordStackLocationMove, hsame,
              evalWordStackMachine, wordStackMachineWriteRegister,
              wordStackMachineBinOp] at heval
            cases heval
            simp [wordStackLocationValue]
      | stack source =>
          simp [wordStackLocationMove, evalWordStackMachine,
            wordStackMachineWriteRegister,
            wordStackMachineBinOp] at heval
          cases heval
          simp [wordStackLocationValue, wordStackOffset]
  | stack destination =>
      cases source with
      | register source =>
          simp [wordStackLocationMove, evalWordStackMachine,
            wordStackMachineWriteRegister,
            wordStackMachineBinOp] at heval
          cases heval
          simp [wordStackLocationValue, wordStackOffset,
            wordStackMachineWriteSlot]
      | stack source =>
          by_cases hsame : destination = source
          · simp [wordStackLocationMove, hsame] at heval
            cases heval
            subst source
            rfl
          · simp [wordStackLocationMove, hsame, evalWordStackMachine,
              wordStackMachineWriteRegister, wordStackMachineWriteSlot] at heval
            cases heval
            simp [wordStackLocationValue, wordStackOffset]

theorem evalWordStackMachine_locationMove_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source other : WordLocation)
    (hotherDestination : other ≠ destination)
    (hotherScratch : other ≠ .register config.scratch)
    (heval : (wordStackLocationMove config destination source).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final other =
      wordStackLocationValue config state other := by
  cases destination with
  | register destination =>
      cases source with
      | register source =>
          cases other with
          | register other =>
              by_cases hsame : destination = source
              · simp [wordStackLocationMove, hsame] at heval
                cases heval
                simp_all [wordStackLocationValue]
              · simp [wordStackLocationMove, hsame,
                  evalWordStackMachine, wordStackMachineWriteRegister,
                  wordStackMachineBinOp] at heval
                cases heval
                simp_all [wordStackLocationValue]
          | stack other =>
              by_cases hsame : destination = source
              · simp [wordStackLocationMove, hsame] at heval
                cases heval
                simp [wordStackLocationValue, wordStackOffset]
              · simp [wordStackLocationMove, hsame, evalWordStackMachine,
                  wordStackMachineWriteRegister, wordStackMachineBinOp] at heval
                cases heval
                simp [wordStackLocationValue, wordStackOffset]
      | stack source =>
          cases other with
          | register other =>
              simp [wordStackLocationMove, evalWordStackMachine,
                wordStackMachineWriteRegister, wordStackMachineBinOp] at heval
              cases heval
              simp_all [wordStackLocationValue]
          | stack other =>
              simp [wordStackLocationMove, evalWordStackMachine,
                wordStackMachineWriteRegister, wordStackMachineBinOp] at heval
              cases heval
              simp [wordStackLocationValue, wordStackOffset]
  | stack destination =>
      cases source with
      | register source =>
          cases other with
          | register other =>
              simp [wordStackLocationMove, evalWordStackMachine,
                wordStackMachineWriteRegister, wordStackMachineWriteSlot,
                wordStackMachineBinOp] at heval
              cases heval
              simp_all [wordStackLocationValue]
          | stack other =>
              simp [wordStackLocationMove, evalWordStackMachine,
                wordStackMachineWriteRegister, wordStackMachineWriteSlot,
                wordStackMachineBinOp] at heval
              cases heval
              simp_all [wordStackLocationValue, wordStackOffset]
      | stack source =>
          cases other with
          | register other =>
              by_cases hsame : destination = source
              · simp [wordStackLocationMove, hsame] at heval
                cases heval
                simp_all [wordStackLocationValue]
              · simp [wordStackLocationMove, hsame, evalWordStackMachine,
                  wordStackMachineWriteRegister, wordStackMachineWriteSlot] at heval
                cases heval
                simp_all [wordStackLocationValue]
          | stack other =>
              by_cases hsame : destination = source
              · simp [wordStackLocationMove, hsame] at heval
                cases heval
                simp_all [wordStackLocationValue, wordStackOffset]
              · simp [wordStackLocationMove, hsame, evalWordStackMachine,
                  wordStackMachineWriteRegister, wordStackMachineWriteSlot] at heval
                cases heval
                simp_all [wordStackLocationValue, wordStackOffset]

theorem evalWordStackMachine_move_preserves_other_value [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source other : Nat)
    (destinationLocation sourceLocation otherLocation : WordLocation)
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hother : wordStackLocation config other = some otherLocation)
    (hdestination_scratch :
      destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (hother_destination : otherLocation ≠ destinationLocation)
    (hother_scratch : otherLocation ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final other =
      wordStackMachineValue config state other := by
  change lookupNatInfo destination config.locations = some destinationLocation
    at hdestination
  change lookupNatInfo source config.locations = some sourceLocation at hsource
  change lookupNatInfo other config.locations = some otherLocation at hother
  simp [wordStackMove] at heval
  cases destinationLocation <;> cases sourceLocation <;>
    cases otherLocation <;>
    simp [evalWordStackMachine, wordStackMachineValue, wordStackLocation,
      wordStackOffset, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, hdestination, hsource, hother] at heval ⊢
  all_goals
    cases heval
    simp_all

theorem evalWordStackMachine_move_preserves_unrelated_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destination source : Nat) (destinationLocation sourceLocation : WordLocation)
    (values : Nat → Option (Word width))
    (hdestination : wordStackLocation config destination =
      some destinationLocation)
    (hsource : wordStackLocation config source = some sourceLocation)
    (hdestination_scratch :
      destinationLocation ≠ .register config.scratch)
    (hsource_scratch : sourceLocation ≠ .register config.scratch)
    (hvalues : wordStackMappedValues config values state)
    (hnoalias : ∀ name value location,
      name ≠ destination →
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ destinationLocation)
    (hno_scratch : ∀ name value location,
      name ≠ destination →
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordStackMove (α := Nat) config destination source).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValuesExcept config destination values final := by
  intro name value location hname hvalue hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hpreserved := evalWordStackMachine_move_preserves_other_value
    config state final destination source name destinationLocation
    sourceLocation location hdestination hsource hlocation
    hdestination_scratch hsource_scratch
    (hnoalias name value location hname hvalue hlocation)
    (hno_scratch name value location hname hvalue hlocation) heval
  rw [hpreserved]
  exact hstateValue

end Flapjack.RiscV
