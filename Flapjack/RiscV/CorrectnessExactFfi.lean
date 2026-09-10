import Flapjack.RiscV.ExactFfi
import Flapjack.RiscV.CorrectnessFfi

/-!
# Correctness equations for the exact RISC-V FFI adapter

These lemmas expose the adapter's semantic contract independently of any
particular oracle implementation. They are the proof seam used when a
compiler-generated ECALL is related to CakeML's `callFfi` transition.
-/

namespace Flapjack.RiscV

/-!
The generated ABI prefix is ordinary RISC-V code.  Once it has run, the
following ECALL is exactly the adapter above; the only arithmetic fact needed
to expose the service number is that it fits in the machine word.
-/
theorem executeInstructionsWithExactFfi_abi [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat)
    (configuration configurationLength array arrayLength : Fin 32)
    (result : ExactRiscVFfiResult width σ)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = result) :
    executeInstructionsWithExactFfi context state
      [.addi 10 configuration (0#width),
       .addi 11 configurationLength (0#width),
       .addi 12 array (0#width),
       .addi 13 arrayLength (0#width),
       .addi 14 0 (BitVec.ofNat width service), .ecall] = result := by
  have hservice_read :
      (readRegister (executeInstructions state.machine
        [.addi 10 configuration (0#width),
         .addi 11 configurationLength (0#width),
         .addi 12 array (0#width),
         .addi 13 arrayLength (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) 14).toNat = service := by
    have hzero' : state.machine.registers 0 = 0 := by
      simpa [readRegister] using hzero
    simp [executeInstructions, execute, writeRegister, readRegister,
      nextPc, hzero', Nat.mod_eq_of_lt hservice_bounded]
  have hresult' : exactRiscVFfiCall context
      { machine := execute (execute (execute (execute
          (execute state.machine (.addi 10 configuration (0#width)))
            (.addi 11 configurationLength (0#width)))
            (.addi 12 array (0#width)))
            (.addi 13 arrayLength (0#width)))
            (.addi 14 0 (BitVec.ofNat width service)),
        ffi := state.ffi } service = result := by
    simpa [executeInstructions] using hresult
  simp only [executeInstructionsWithExactFfi, executeWithExactFfi]
  have hservice_read' :
      (readRegister
        (execute (execute (execute (execute
          (execute state.machine (.addi 10 configuration (0#width)))
            (.addi 11 configurationLength (0#width)))
            (.addi 12 array (0#width)))
            (.addi 13 arrayLength (0#width)))
            (.addi 14 0 (BitVec.ofNat width service))) 14).toNat = service := by
    simpa [executeInstructions] using hservice_read
  rw [hservice_read', hresult']
  cases result <;> rfl

/-! The compiler-facing form of the ABI theorem.  The Word selector emits
    register moves from natural-number locations, whereas the exact machine
    boundary consumes `Fin 32` registers.  Keeping this conversion here makes
    the generated FFI code usable in a pass-level correctness proof without
    repeating the selector's list-shape calculation. -/
theorem wordFfiToRiscV_exactFfi_simulation [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Fin 32)
    (service : Nat) (code : List (Instruction width))
    (result : ExactRiscVFfiResult width σ)
    (hservice : lookupWordFfiService function context.services = some service)
    (hcode : wordFfiToRiscV context function configuration.val
        configurationLength.val array.val arrayLength.val = some code)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = result) :
    executeInstructionsWithExactFfi context state code = result := by
  have hcode' : code =
      [.addi 10 configuration (0#width),
       .addi 11 configurationLength (0#width),
       .addi 12 array (0#width),
       .addi 13 arrayLength (0#width),
       .addi 14 0 (BitVec.ofNat width service), .ecall] := by
    simp [wordFfiToRiscV, hservice, wordRegisterMoves, registerOfNat] at hcode
    exact hcode.symm
  rw [hcode']
  apply executeInstructionsWithExactFfi_abi context state service
    configuration configurationLength array arrayLength result hservice_bounded hzero
  exact hresult

/-! The loop-aware selector delegates an FFI leaf to the same Word selector,
    but its result is wrapped in labelled-control lowering.  This bridge keeps
    that normalization explicit so a control-flow-aware pipeline can consume
    the exact FFI theorem without reopening the mutual selector definition. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_simulation
    [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Fin 32)
    (service : Nat) (code : List (Instruction width))
    (result : ExactRiscVFfiResult width σ)
    (hservice : lookupWordFfiService function context.services = some service)
    (hcode : wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := context.services } : WordCallFfiContext width)
      (.ffi function configuration.val configurationLength.val array.val
        arrayLength.val ([], [])) = some (code, []))
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = result) :
    executeInstructionsWithExactFfi context state code = result := by
  have hagree := wordFunctionToRiscVWithCallsAndFfiAndLoops_agrees_straightLine
    ({ targets := [], services := context.services } : WordCallFfiContext width)
    (.ffi function configuration.val configurationLength.val array.val
      arrayLength.val ([], []) : WordProg (Word width))
    (WordRiscVFFIStraightLine.ffi function configuration.val
      configurationLength.val array.val arrayLength.val ([], []))
  have hwordCode : wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := context.services } : WordCallFfiContext width)
      (.ffi function configuration.val configurationLength.val array.val
        arrayLength.val ([], [])) = some (code, []) := by
    rw [← hagree]
    exact hcode
  have hcode' : wordFfiToRiscV context function configuration.val
      configurationLength.val array.val arrayLength.val = some code := by
    cases hffi : wordFfiToRiscV (width := width) context function configuration.val
        configurationLength.val array.val arrayLength.val with
    | none =>
        simp [wordFunctionToRiscVWithCallsAndFfi, hffi] at hwordCode
    | some ffiCode =>
        have hpair : (ffiCode, ([] : List (Fin 32))) =
            (code, ([] : List (Fin 32))) := by
          simpa [wordFunctionToRiscVWithCallsAndFfi, hffi] using hwordCode
        cases hpair
        rfl
  exact wordFfiToRiscV_exactFfi_simulation context state function
    configuration configurationLength array arrayLength service code result
    hservice hcode' hservice_bounded hzero hresult

/-! The same FFI leaf theorem remains valid in the real call-aware context.
    The target table is carried by the complete compiler even when this leaf
    does not perform a call; making it explicit avoids weakening a later
    pass-level theorem to the singleton empty-target fixture above. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_simulation_targets
    [NeZero width]
    (context : WordFfiContext)
    (targets : List (Nat × Word width × List Nat × List Nat))
    (state : ExactRiscVFfiState width σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Fin 32)
    (service : Nat) (code : List (Instruction width))
    (result : ExactRiscVFfiResult width σ)
    (hservice : lookupWordFfiService function context.services = some service)
    (hcode : wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := targets, services := context.services } : WordCallFfiContext width)
      (.ffi function configuration.val configurationLength.val array.val
        arrayLength.val ([], [])) = some (code, []))
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = result) :
    executeInstructionsWithExactFfi context state code = result := by
  have hagree := wordFunctionToRiscVWithCallsAndFfiAndLoops_agrees_straightLine
    ({ targets := targets, services := context.services } : WordCallFfiContext width)
    (.ffi function configuration.val configurationLength.val array.val
      arrayLength.val ([], []) : WordProg (Word width))
    (WordRiscVFFIStraightLine.ffi function configuration.val
      configurationLength.val array.val arrayLength.val ([], []))
  have hwordCode : wordFunctionToRiscVWithCallsAndFfi
      ({ targets := targets, services := context.services } : WordCallFfiContext width)
      (.ffi function configuration.val configurationLength.val array.val
        arrayLength.val ([], [])) = some (code, []) := by
    rw [← hagree]
    exact hcode
  have hcode' : wordFfiToRiscV context function configuration.val
      configurationLength.val array.val arrayLength.val = some code := by
    cases hffi : wordFfiToRiscV (width := width) context function configuration.val
        configurationLength.val array.val arrayLength.val with
    | none =>
        simp [wordFunctionToRiscVWithCallsAndFfi, hffi] at hwordCode
    | some ffiCode =>
        have hpair : (ffiCode, ([] : List (Fin 32))) =
            (code, ([] : List (Fin 32))) := by
          simpa [wordFunctionToRiscVWithCallsAndFfi, hffi] using hwordCode
        cases hpair
        rfl
  exact wordFfiToRiscV_exactFfi_simulation context state function
    configuration configurationLength array arrayLength service code result
    hservice hcode' hservice_bounded hzero hresult

theorem executeInstructionsWithExactFfiCounted_normal
    [NeZero width]
    (context : WordFfiContext)
    (state final : ExactRiscVFfiState width σ)
    (instructions : List (Instruction width))
    (hresult : executeInstructionsWithExactFfi context state instructions =
      .normal final) :
    executeInstructionsWithExactFfiCounted context state instructions =
      (.normal final, instructions.length) := by
  induction instructions generalizing state final with
  | nil =>
      simp [executeInstructionsWithExactFfi,
        executeInstructionsWithExactFfiCounted] at hresult ⊢
      cases hresult
      rfl
  | cons instruction instructions ih =>
      cases hstep : executeWithExactFfi context state instruction with
      | normal nextState =>
          have htail : executeInstructionsWithExactFfi context nextState instructions =
              .normal final := by
            simpa [executeInstructionsWithExactFfi, hstep] using hresult
          have hcount := ih nextState final htail
          simp [executeInstructionsWithExactFfiCounted, hstep, hcount,
            List.length]
      | final terminalState event =>
          simp [executeInstructionsWithExactFfi, hstep] at hresult
      | error terminalState =>
          simp [executeInstructionsWithExactFfi, hstep] at hresult

/-! Counted version of the compiler-facing exact FFI boundary.  The result
    hypothesis is restricted to the normal case because a final FFI event
    intentionally short-circuits the remaining instruction list. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_counted_simulation_targets
    [NeZero width]
    (context : WordFfiContext)
    (targets : List (Nat × Word width × List Nat × List Nat))
    (state final : ExactRiscVFfiState width σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Fin 32)
    (service : Nat) (code : List (Instruction width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hcode : wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := targets, services := context.services } : WordCallFfiContext width)
      (.ffi function configuration.val configurationLength.val array.val
        arrayLength.val ([], [])) = some (code, []))
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state.machine 0 = 0)
    (hresult : exactRiscVFfiCall context
        { machine := executeInstructions state.machine
            [.addi 10 configuration (0#width),
             .addi 11 configurationLength (0#width),
             .addi 12 array (0#width),
             .addi 13 arrayLength (0#width),
             .addi 14 0 (BitVec.ofNat width service)],
          ffi := state.ffi } service = .normal final) :
    executeInstructionsWithExactFfiCounted context state code =
      (.normal final, code.length) := by
  have hrun := wordFunctionToRiscVWithCallsAndFfiAndLoops_exactFfi_simulation_targets
    context targets state function configuration configurationLength array arrayLength
    service code (.normal final) hservice hcode hservice_bounded hzero hresult
  apply executeInstructionsWithExactFfiCounted_normal context state final code
  exact hrun

theorem exactWriteBytesAux_pc [NeZero width] (address : Word width)
    (state : State width) (offset : Nat) (bytes : List UInt8) :
    (exactWriteBytesAux address state offset bytes).pc = state.pc := by
  induction bytes generalizing state offset with
  | nil => rfl
  | cons byte bytes induction =>
      simp only [exactWriteBytesAux]
      exact induction (state :=
        writeByte state (byteAddress address offset) (BitVec.ofNat 8 byte.toNat))
        (offset := offset + 1)

theorem exactWriteBytes_pc [NeZero width] (state : State width)
    (address : Word width) (bytes : List UInt8) :
    (exactWriteBytes state address bytes).pc = state.pc := by
  exact exactWriteBytesAux_pc address state 0 bytes

theorem exactRiscVFfiCall_return [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (nextState : σ) (nextBytes : List UInt8)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .returned nextState nextBytes)
    (hlength : nextBytes.length =
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat).length) :
    exactRiscVFfiCall context state service =
      .normal
        { machine :=
            { exactWriteBytes state.machine (readRegister state.machine 12)
                nextBytes with
              pc := nextPc state.machine }
          ffi :=
            { state.ffi with
              state := nextState
              ioEvents := state.ffi.ioEvents ++
                [{ name := .extCall function,
                   configuration := exactReadBytes state.machine
                     (readRegister state.machine 10)
                     (readRegister state.machine 11).toNat,
                   bytes :=
                     (exactReadBytes state.machine
                       (readRegister state.machine 12)
                       (readRegister state.machine 13).toNat).zip nextBytes }] } } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle, hlength]
  change (exactWriteBytes state.machine (readRegister state.machine 12) nextBytes).pc + 4 =
    state.machine.pc + 4
  rw [exactWriteBytes_pc]

theorem exactRiscVFfiCall_final [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (outcome : FfiOutcome)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .final outcome) :
    exactRiscVFfiCall context state service =
      .final state
        { name := .extCall function,
          configuration := exactReadBytes state.machine
            (readRegister state.machine 10)
            (readRegister state.machine 11).toNat,
          bytes := exactReadBytes state.machine
            (readRegister state.machine 12)
            (readRegister state.machine 13).toNat,
          outcome := outcome } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle]

theorem exactRiscVFfiCall_length_failure [NeZero width]
    (context : WordFfiContext)
    (state : ExactRiscVFfiState width σ)
    (service : Nat) (function : FunName)
    (nextState : σ) (nextBytes : List UInt8)
    (hservice : lookupWordFfiName service context.services = some function)
    (hfunction : function ≠ "")
    (horacle : state.ffi.oracle (.extCall function) state.ffi.state
      (exactReadBytes state.machine (readRegister state.machine 10)
        (readRegister state.machine 11).toNat)
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat) =
      .returned nextState nextBytes)
    (hlength : nextBytes.length ≠
      (exactReadBytes state.machine (readRegister state.machine 12)
        (readRegister state.machine 13).toNat).length) :
    exactRiscVFfiCall context state service =
      .final state
        { name := .extCall function,
          configuration := exactReadBytes state.machine
            (readRegister state.machine 10)
            (readRegister state.machine 11).toNat,
          bytes := exactReadBytes state.machine
            (readRegister state.machine 12)
            (readRegister state.machine 13).toNat,
          outcome := .failed } := by
  simp [exactRiscVFfiCall, hservice, callFfi, hfunction, horacle, hlength]

end Flapjack.RiscV
