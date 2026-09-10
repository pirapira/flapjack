import Flapjack.RiscV.CorrectnessExactFfi
import Flapjack.Test.ExactFfi

namespace Flapjack.RiscV

def exactFfiAbiState : ExactRiscVFfiState 64 Unit :=
  { exactFfiState with
    machine :=
      let machine := writeRegister exactFfiState.machine 10 10
      let machine := writeRegister machine 11 1
      let machine := writeRegister machine 12 20
      writeRegister machine 13 2 }

def exactFfiMismatchState : ExactRiscVFfiState 64 Unit :=
  { exactFfiAbiState with
    ffi :=
      { exactFfiAbiState.ffi with
        oracle := fun _ state _ _ => .returned state [9] } }

def exactFfiSetupInstructions : List (Instruction 64) :=
  [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
   .addi 14 0 (BitVec.ofNat 64 7)]

example :
    executeInstructionsWithExactFfi
        { services := [(echo, 7)] } exactFfiState
        exactFfiSetupInstructions =
      .normal { exactFfiState with
        machine := executeInstructions exactFfiState.machine
          exactFfiSetupInstructions } := by
  apply executeInstructionsWithExactFfi_of_no_ecall
  intro instruction hinstruction
  simp [exactFfiSetupInstructions] at hinstruction
  rcases hinstruction with rfl | rfl | rfl | rfl | rfl <;> decide

example :
    executeInstructionsWithExactFfi
        { services := [(echo, 7)] } exactFfiState
        (exactFfiSetupInstructions ++ [.ecall]) =
      match executeInstructionsWithExactFfi
          { services := [(echo, 7)] } exactFfiState
          exactFfiSetupInstructions with
      | .normal middle =>
          executeInstructionsWithExactFfi
            { services := [(echo, 7)] } middle [.ecall]
      | result => result := by
  apply executeInstructionsWithExactFfi_append

example :
    executeInstructionsWithExactFfi
        { services := [("echo", 7)] } exactFfiState
        [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      exactRiscVFfiCall { services := [("echo", 7)] }
        { machine := executeInstructions exactFfiState.machine
            [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
             .addi 14 0 (BitVec.ofNat 64 7)],
          ffi := exactFfiState.ffi } 7 := by
  apply executeInstructionsWithExactFfi_abi
  · decide
  · simp [exactFfiState, exactFfiMachineWithBytes, exactFfiMachine,
      zeroState, readRegister, writeRegister]
  · rfl

example :
    executeInstructionsWithExactFfi
        { services := [("echo", 7)] } exactFfiState
        [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      exactRiscVFfiCall { services := [("echo", 7)] }
        { machine := executeInstructions exactFfiState.machine
            [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
             .addi 14 0 (BitVec.ofNat 64 7)],
          ffi := exactFfiState.ffi } 7 := by
  apply wordFfiToRiscV_exactFfi_simulation
    (context := { services := [("echo", 7)] })
    (state := exactFfiState) (function := "echo")
    (configuration := 1) (configurationLength := 2)
    (array := 3) (arrayLength := 4) (service := 7)
    (code := [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
      .addi 14 0 (BitVec.ofNat 64 7), .ecall])
    (result := exactRiscVFfiCall { services := [("echo", 7)] }
      { machine := executeInstructions exactFfiState.machine
          [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
           .addi 14 0 (BitVec.ofNat 64 7)],
        ffi := exactFfiState.ffi } 7)
  · rfl
  · decide
  · decide
  · simp [exactFfiState, exactFfiMachineWithBytes, exactFfiMachine,
      zeroState, readRegister, writeRegister]
  · rfl

example :
    executeInstructionsWithExactFfi
        { services := [("echo", 7)] } exactFfiState
        [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      exactRiscVFfiCall { services := [("echo", 7)] }
        { machine := executeInstructions exactFfiState.machine
            [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
             .addi 14 0 (BitVec.ofNat 64 7)],
          ffi := exactFfiState.ffi } 7 := by
  apply wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_simulation_targets
    (context := { services := [("echo", 7)] })
    (targets := [(99, BitVec.ofNat 64 100, [2], [10])])
    (state := exactFfiState) (function := "echo")
    (configuration := 1) (configurationLength := 2)
    (array := 3) (arrayLength := 4) (service := 7)
    (code := [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
      .addi 14 0 (BitVec.ofNat 64 7), .ecall])
    (result := exactRiscVFfiCall { services := [("echo", 7)] }
      { machine := executeInstructions exactFfiState.machine
          [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
           .addi 14 0 (BitVec.ofNat 64 7)],
        ffi := exactFfiState.ffi } 7)
  · rfl
  · simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
      wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
      wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
      lookupWordFfiService, wordRegisterMoves, registerOfNat,
      wordControlInstructions]
  · decide
  · simp [exactFfiState, exactFfiMachineWithBytes, exactFfiMachine,
      zeroState, readRegister, writeRegister]
  · rfl

example (final : ExactRiscVFfiState 64 Unit)
    (hcall : exactRiscVFfiCall { services := [("echo", 7)] }
        { machine := executeInstructions exactFfiState.machine
            [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
             .addi 14 0 (BitVec.ofNat 64 7)],
          ffi := exactFfiState.ffi } 7 = .normal final) :
    executeInstructionsWithExactFfiCounted
        { services := [("echo", 7)] } exactFfiState
        [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      (.normal final, 6) := by
  apply wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_counted_simulation_targets
    (context := { services := [("echo", 7)] })
    (targets := [(99, BitVec.ofNat 64 100, [2], [10])])
    (state := exactFfiState) (final := final) (function := "echo")
    (configuration := 1) (configurationLength := 2)
    (array := 3) (arrayLength := 4) (service := 7)
    (code := [.addi 10 1 0, .addi 11 2 0, .addi 12 3 0, .addi 13 4 0,
      .addi 14 0 (BitVec.ofNat 64 7), .ecall])
  · rfl
  · simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
      wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
      wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
      lookupWordFfiService, wordRegisterMoves, registerOfNat,
      wordControlInstructions]
  · decide
  · simp [exactFfiState, exactFfiMachineWithBytes, exactFfiMachine,
      zeroState, readRegister, writeRegister]
  · exact hcall

example :
    exactRiscVFfiCall
        { services := [("echo", 7)] } exactFfiAbiState 7 =
      .normal
        { machine :=
            { exactWriteBytes exactFfiAbiState.machine
                (readRegister exactFfiAbiState.machine 12) [9, 8] with
              pc := nextPc exactFfiAbiState.machine }
          ffi :=
            { exactFfiAbiState.ffi with
              state := ()
              ioEvents :=
                [{ name := .extCall "echo",
                   configuration := exactReadBytes exactFfiAbiState.machine
                     (readRegister exactFfiAbiState.machine 10)
                     (readRegister exactFfiAbiState.machine 11).toNat,
                   bytes :=
                     (exactReadBytes exactFfiAbiState.machine
                       (readRegister exactFfiAbiState.machine 12)
                       (readRegister exactFfiAbiState.machine 13).toNat).zip [9, 8] }] } } := by
  exact exactRiscVFfiCall_return
    (context := { services := [("echo", 7)] })
    (state := exactFfiAbiState) (service := 7)
    (function := "echo") (nextState := ()) (nextBytes := [9, 8])
    (by decide)
    (by decide)
    (by
      simp only [exactFfiAbiState, exactFfiState]
      congr 1)
    (by decide)

example :
    exactFfiResultBytes 20 2 [9, 8]
        (exactRiscVFfiCall { services := [("echo", 7)] } exactFfiAbiState 7) = true ∧
    exactFfiResultEvents
      [{ name := .extCall "echo", configuration := [42],
         bytes := [(9, 9), (8, 8)] }]
      (exactRiscVFfiCall { services := [("echo", 7)] } exactFfiAbiState 7) = true := by
  decide

def exactFfiResultFinalFailure :
    ExactRiscVFfiResult 64 Unit → Bool
  | .final _ event =>
      event.name == .extCall "echo" && event.configuration == [42] &&
        event.bytes == [9, 8] && event.outcome == .failed
  | .normal _ | .error _ => false

example :
    exactFfiResultFinalFailure
        (exactRiscVFfiCall { services := [("echo", 7)] }
          exactFfiMismatchState 7) = true := by
  decide

end Flapjack.RiscV
