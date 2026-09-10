import Flapjack.RiscV.CorrectnessFfiMachine
import Flapjack.RiscV.Lab
import Flapjack.RiscV.ExactFfi
import Flapjack.RiscV.CorrectnessExactFfi

/-!
# Pipeline FFI machine correctness

This module closes the small gap between the executable
Word-to-Stack/StackRemove/LabLang pipeline and the RISC-V FFI machine
boundary.  The compiler theorem is concrete about the register allocation,
while the host and initial machine state remain abstract.
-/

namespace Flapjack.RiscV

def pipelineFfiWordConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7)]
    scratch := 31
    stackBase := 21 }

def pipelineFfiWordConfigSource : WordStackConfig :=
  { locations := [(4, .register 4), (5, .register 5),
      (6, .register 6), (7, .register 7)]
    scratch := 31
    stackBase := 21 }

def pipelineFfiStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

theorem compileWordProgramNatToRiscV_pipeline_ffi :
    compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfig
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat) =
      some [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
        .addi 0 0 (BitVec.ofNat 64 28),
        .addi 14 0 (BitVec.ofNat 64 7), .ecall] := by
  decide +kernel

theorem compileWordProgramNatToRiscV_pipeline_ffi_source :
    compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfigSource
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 4 5 6 7 ([], []) : WordProg Nat) =
      some [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
        .addi 0 0 (BitVec.ofNat 64 28),
        .addi 14 0 (BitVec.ofNat 64 7), .ecall] := by
  decide +kernel

theorem executeCompiledPipelineFfi
    (host : WordFfiHost 64) (state : State 64)
    (hzero : readRegister state 0 = 0) :
    (compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfig
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 0 1 2 3 ([], []) : WordProg Nat)).bind
        (executeInstructionsWithFfi host state) =
      host 7 (readRegister state 4) (readRegister state 5)
        (readRegister state 6) (readRegister state 7)
        (executeInstructions state
          [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
            .addi 0 0 (BitVec.ofNat 64 28),
            .addi 14 0 (BitVec.ofNat 64 7)]) := by
  rw [compileWordProgramNatToRiscV_pipeline_ffi]
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  simp [executeInstructionsWithFfi, executeWithFfi, executeInstructions,
    execute, writeRegister, readRegister, nextPc, hzero']

theorem executeCompiledPipelineFfi_source_agreement
    (host : WordFfiHost 64)
    (handler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
      State 64 → Option (State 64))
    (state : State 64)
    (hzero : readRegister state 0 = 0)
    (hhandler : host 7 (readRegister state 4) (readRegister state 5)
        (readRegister state 6) (readRegister state 7)
        (executeInstructions state
          [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
           .addi 0 0 (BitVec.ofNat 64 28),
           .addi 14 0 (BitVec.ofNat 64 7)]) =
      handler "echo" (readRegister state 4) (readRegister state 5)
        (readRegister state 6) (readRegister state 7) state) :
    (compileWordProgramNatToRiscV (width := 64)
      { services := [("echo", 7)] } pipelineFfiWordConfigSource
      pipelineFfiStackRemoveConfig 2 3
      (.ffi "echo" 4 5 6 7 ([], []) : WordProg Nat)).bind
        (fun code =>
          (executeInstructionsWithFfi host state code).map
            (fun final => (final, ([] : List (Word 64))))) =
      evalWordFunctionWithCallsAndFfi [] handler 1 state
        (.ffi "echo" 4 5 6 7 ([], [])) := by
  have hmachine := executeCompiledPipelineFfi host state hzero
  rw [compileWordProgramNatToRiscV_pipeline_ffi] at hmachine
  simp only [Option.bind_some] at hmachine
  rw [compileWordProgramNatToRiscV_pipeline_ffi_source]
  have hmap (result : Option (State 64)) :
      result.map (fun final => (final, ([] : List (Word 64)))) =
        result.bind (fun final => some (final, [])) := by
    cases result <;> rfl
  simpa [hmachine, evalWordFunctionWithCallsAndFfi, evalWordFfi, registerOfNat,
    hhandler] using
    hmap (handler "echo" (readRegister state 4) (readRegister state 5)
      (readRegister state 6) (readRegister state 7) state)

theorem executeCompiledPipelineExactFfi
    (state : ExactRiscVFfiState 64 sigma)
    (hzero : readRegister state.machine 0 = 0) :
    executeInstructionsWithExactFfi
        { services := [("echo", 7)] } state
        [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
         .addi 0 0 (BitVec.ofNat 64 28),
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      exactRiscVFfiCall { services := [("echo", 7)] }
        { state with machine := (executeInstructions state.machine
            [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
             .addi 0 0 (BitVec.ofNat 64 28),
             .addi 14 0 (BitVec.ofNat 64 7)]) } 7 := by
  have hzero' : state.machine.registers 0 = 0 := by
    simpa [readRegister] using hzero
  have hecall := executeInstructionsWithExactFfi_ecall
    ({ services := [("echo", 7)] } : WordFfiContext)
    ({ state with machine := (executeInstructions state.machine
        [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
         .addi 0 0 (BitVec.ofNat 64 28),
         .addi 14 0 (BitVec.ofNat 64 7)]) })
  simpa [executeInstructionsWithExactFfi, executeWithExactFfi,
    executeInstructions, execute, writeRegister, readRegister,
    nextPc, hzero'] using hecall

theorem executeCompiledPipelineExactFfi_counted
    (state final : ExactRiscVFfiState 64 sigma)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall { services := [("echo", 7)] }
        { state with machine := (executeInstructions state.machine
            [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
             .addi 0 0 (BitVec.ofNat 64 28),
             .addi 14 0 (BitVec.ofNat 64 7)]) } 7 = .normal final) :
    executeInstructionsWithExactFfiCounted
        { services := [("echo", 7)] } state
        [.or 10 4 4, .or 11 5 5, .or 12 6 6, .or 13 7 7,
         .addi 0 0 (BitVec.ofNat 64 28),
         .addi 14 0 (BitVec.ofNat 64 7), .ecall] =
      (.normal final, 7) := by
  apply executeInstructionsWithExactFfiCounted_normal
  rw [executeCompiledPipelineExactFfi state hzero]
  exact hresult

end Flapjack.RiscV
