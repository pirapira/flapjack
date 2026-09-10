import Flapjack.RiscV.Ffi
import Flapjack.RiscV.Lab
import Flapjack.RiscV.StepCorrectness

/-!
Machine-level correctness for the RISC-V FFI ABI.  The abstract Word FFI
handler receives the four source-register values and the pre-call state.  The
target host instead receives the state after the four ABI moves and service
materialization.  These theorems make that boundary explicit.
-/

namespace Flapjack.RiscV

theorem executeInstructionsWithFfi_append
    [NeZero width] (host : WordFfiHost width) (state : State width)
    (first second : List (Instruction width)) :
    executeInstructionsWithFfi host state (first ++ second) =
      (executeInstructionsWithFfi host state first).bind
        (fun state => executeInstructionsWithFfi host state second) := by
  induction first generalizing state with
  | nil => simp [executeInstructionsWithFfi]
  | cons instruction first ih =>
      simp only [List.cons_append, executeInstructionsWithFfi]
      cases hstep : executeWithFfi host state instruction with
      | none => simp []
      | some nextState => simp [ih]

/-! Register marshalling is made only of `addi` instructions, so it cannot
invoke the host.  This connects the ordinary execution equation for the
generated move prefix to the FFI-aware runner. -/
theorem executeInstructionsWithFfi_wordRegisterMoves [NeZero width]
    (host : WordFfiHost width) (state : State width)
    (registerMoves : List (Nat × Nat)) (code : List (Instruction width))
    (hcode : wordRegisterMoves (width := width) registerMoves = some code) :
    executeInstructionsWithFfi host state code =
      some (executeInstructions state code) := by
  induction registerMoves generalizing state code with
  | nil =>
      simp [wordRegisterMoves] at hcode
      subst code
      simp [executeInstructionsWithFfi, executeInstructions]
  | cons move registerMoves ih =>
      cases move with
      | mk destination source =>
          cases hdestination : registerOfNat destination with
          | none => simp [wordRegisterMoves, hdestination] at hcode
          | some destinationRegister =>
              cases hsource : registerOfNat source with
              | none => simp [wordRegisterMoves, hdestination, hsource] at hcode
              | some sourceRegister =>
                  cases hmoves : wordRegisterMoves (width := width) registerMoves with
                  | none =>
                      simp [wordRegisterMoves, hdestination, hsource, hmoves]
                        at hcode
                  | some rest =>
                      have hrest : wordRegisterMoves (width := width) registerMoves = some rest :=
                        hmoves
                      have hcode' :
                          (.addi destinationRegister sourceRegister 0 :: rest) = code := by
                        simpa [wordRegisterMoves, hdestination, hsource, hmoves]
                          using hcode
                      subst code
                      simp only [executeInstructionsWithFfi, executeInstructions,
                        executeWithFfi]
                      change executeInstructionsWithFfi host
                          (execute state
                            (.addi destinationRegister sourceRegister 0)) rest =
                        some (executeInstructions
                          (execute state
                            (.addi destinationRegister sourceRegister 0)) rest)
                      rw [ih (execute state
                        (.addi destinationRegister sourceRegister 0)) rest hrest]

/-!
The Lab FFI operation is the point at which the already-marshalled Word ABI
is handed to the target machine.  Its compiler expansion only materializes
the service number in x14 and then executes ECALL; the four argument
registers are intentionally preserved.  This lemma exposes that boundary in
a form that can be composed with Lab section and program compilation.
-/
theorem labCompileAsm_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat)
    (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (labCompileAsm context sectionId labels position (.callFfi function)).bind
        (executeInstructionsWithFfi host state) = resultState := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  simpa [labCompileAsm, hservice, executeInstructionsWithFfi, executeWithFfi,
    executeInstructions, execute, writeRegister, readRegister, nextPc,
    hzero', Nat.mod_eq_of_lt hservice_bounded] using hhost

/-!
Lift the instruction-level result through the section compiler for the
singleton FFI section.  This keeps label collection and the generated code
shape behind a reusable semantic boundary for later linked-program proofs.
-/
theorem compileLabSection_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (compileLabSection context
      ⟨sectionId, [.labAsm (.callFfi function) [] 0]⟩).bind
        (executeInstructionsWithFfi host state) = resultState := by
  simp [compileLabSection, labCompileLines, labCompileAsm]
  exact labCompileAsm_callFfi_execute_agreement context host state sectionId
    [] 0 function service resultState hservice hservice_bounded hzero hhost

/-!
The corresponding one-section program theorem closes the next linking
boundary.  Since the section contains no labels, flattening preserves the
same service materialization and ECALL sequence proved above.
-/
theorem compileLabProgram_callFfi_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (state : State width)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (resultState : Option (State width))
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (readRegister state 10) (readRegister state 11)
      (readRegister state 12) (readRegister state 13)
      (executeInstructions state
        [.addi 14 0 (BitVec.ofNat width service)]) = resultState) :
    (compileLabProgram context
      [⟨sectionId, [.labAsm (.callFfi function) [] 0]⟩]).bind
        (executeInstructionsWithFfi host state) = resultState := by
  simp [compileLabProgram, labCompileProgramSections, labCompileProgramLines,
    labCompileAsmProgram]
  exact labCompileAsm_callFfi_execute_agreement context host state sectionId
    [] 0 function service resultState hservice hservice_bounded hzero hhost

/-!
At the function boundary, an FFI call must return through the caller's x1
continuation.  This theorem composes the linked program shape, ECALL host
transition, and JALR x0, x1, 0 return path for the smallest call-and-return
function.  The fixed four-step fuel is the exact cost of the generated
addi, ecall, jalr, and return-address check.
-/
theorem compileLabProgram_callFfi_return_executeFunctionAt_agreement
    (context : WordFfiContext)
    (host : WordFfiHost 64) (state hostState : State 64)
    (sectionId : Nat) (function : FunName) (service : Nat)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ 64)
    (hzero : readRegister state 0 = 0)
    (hhost : host service
      (state.registers 10) (state.registers 11)
      (state.registers 12) (state.registers 13)
      { pc := 4, registers := fun current =>
          if current = 14 then BitVec.ofNat 64 service
          else state.registers current,
        memory := state.memory, privilege := state.privilege, mode := state.mode } =
      some hostState)
    (hhost_pc : hostState.pc = 8)
    (hhost_return : readRegister hostState 1 = BitVec.ofNat 64 100) :
    (compileLabProgram context
      [⟨sectionId, [
        .labAsm (.callFfi function) [] 0,
        .labAsm (.return) [] 0]⟩]).bind
    (fun code =>
          (executeFunctionAtWithFfi host 4 0 0 (BitVec.ofNat 64 100)
            [] code [] [] state)) = some [] := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  let afterAddi : State 64 :=
    { pc := 4, registers := fun current =>
        if current = 14 then BitVec.ofNat 64 service
        else state.registers current,
      memory := state.memory, privilege := state.privilege, mode := state.mode }
  have hadd :
      execute { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service)) = afterAddi := by
    simp [afterAddi, execute, writeRegister, readRegister, nextPc, hzero']
  have haddWithFfi :
      executeWithFfi host { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service)) = some afterAddi := by
    simpa [executeWithFfi] using congrArg some hadd
  have hecall :
      executeWithFfi host afterAddi .ecall = some hostState := by
    simpa [executeWithFfi, afterAddi, readRegister,
      Nat.mod_eq_of_lt hservice_bounded] using hhost
  have hhost_return' : hostState.registers 1 = BitVec.ofNat 64 100 := by
    simpa [readRegister] using hhost_return
  have hmask :
      (BitVec.ofNat 64 100) &&& (BitVec.ofNat 64 (2 ^ 64 - 2)) =
        BitVec.ofNat 64 100 := by
    decide
  have hreturn :
      execute hostState (.jalr 0 1 (0#64)) = { hostState with pc := 100 } := by
    simp [execute, writeRegister, readRegister, hhost_return', hmask]
  have hrun :
      executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { state with pc := 0 } =
      some { hostState with pc := 100 } := by
    have hzeroNe : (0#64) ≠ (BitVec.ofNat 64 100) := by decide
    have hfourNe : (4#64) ≠ (BitVec.ofNat 64 100) := by decide
    have hfirst :
        executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { state with pc := 0 } =
          executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            afterAddi := by
      rw [executeCodeUntilWithFfi]
      simp [hzeroNe]
      change
        (executeWithFfi host { state with pc := 0 }
          (.addi 14 0 (BitVec.ofNat 64 service))).bind
            (fun nextState =>
              executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
                [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
                nextState) = _
      rw [haddWithFfi]
      simp
    have hsecond :
        executeCodeUntilWithFfi host 3 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            afterAddi =
          executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            hostState := by
      rw [executeCodeUntilWithFfi]
      simp [afterAddi, hfourNe]
      change
        (executeWithFfi host afterAddi .ecall).bind
            (fun nextState =>
              executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
                [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
                nextState) = _
      rw [hecall]
      simp
    have hreturnWithFfi :
        executeWithFfi host hostState (.jalr 0 1 (0#64)) =
          some { hostState with pc := 100 } := by
      simpa [executeWithFfi] using congrArg some hreturn
    have hthird :
        executeCodeUntilWithFfi host 2 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            hostState =
          executeCodeUntilWithFfi host 1 (0#64) (BitVec.ofNat 64 100)
            [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
            { hostState with pc := 100 } := by
      simp [executeCodeUntilWithFfi, hreturnWithFfi, hhost_pc]
    rw [hfirst, hsecond, hthird]
    simp [executeCodeUntilWithFfi]
  have hcode :
      compileLabProgram context
        [⟨sectionId, [
          .labAsm (.callFfi function) [] 0,
          .labAsm (.return) [] 0]⟩] =
        some [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0] := by
    simp [compileLabProgram, labCompileProgramSections,
      labCompileProgramLines, labCompileAsmProgram, hservice]
  rw [hcode]
  change
    (executeCodeUntilWithFfi host 4 (0#64) (BitVec.ofNat 64 100)
      [.addi 14 0 (BitVec.ofNat 64 service), .ecall, .jalr 0 1 0]
      { state with pc := 0 }).map (fun _ => ([] : List (Word 64))) =
      some []
  rw [hrun]
  simp

theorem executeInstructionsWithFfi_wordFfi_abi
    [NeZero width] (host : WordFfiHost width) (state : State width)
    (service : Nat) (configuration configurationLength array arrayLength : Fin 32)
    (resultState : Option (State width))
    (hservice_bounded : service < 2 ^ width)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configuration, configurationLength, array, arrayLength] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhost : host service
      (readRegister state configuration)
      (readRegister state configurationLength)
      (readRegister state array)
      (readRegister state arrayLength)
      (executeInstructions state
        [.addi 10 configuration (0#width), .addi 11 configurationLength (0#width),
         .addi 12 array (0#width), .addi 13 arrayLength (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      resultState) :
      executeInstructionsWithFfi host state
      [.addi 10 configuration (0#width), .addi 11 configurationLength (0#width),
       .addi 12 array (0#width), .addi 13 arrayLength (0#width),
       .addi 14 0 (BitVec.ofNat width service), .ecall] =
      resultState := by
  have hzero' : state.registers 0 = 0 := by
    simpa [readRegister] using hzero
  have hconfiguration10 : configuration ≠ 10 :=
    hsource configuration (by simp) 10 (by simp)
  have hconfiguration11 : configuration ≠ 11 :=
    hsource configuration (by simp) 11 (by simp)
  have hconfiguration12 : configuration ≠ 12 :=
    hsource configuration (by simp) 12 (by simp)
  have hconfiguration13 : configuration ≠ 13 :=
    hsource configuration (by simp) 13 (by simp)
  have hconfigurationLength10 : configurationLength ≠ 10 :=
    hsource configurationLength (by simp) 10 (by simp)
  have hconfigurationLength11 : configurationLength ≠ 11 :=
    hsource configurationLength (by simp) 11 (by simp)
  have hconfigurationLength12 : configurationLength ≠ 12 :=
    hsource configurationLength (by simp) 12 (by simp)
  have hconfigurationLength13 : configurationLength ≠ 13 :=
    hsource configurationLength (by simp) 13 (by simp)
  have harray10 : array ≠ 10 :=
    hsource array (by simp) 10 (by simp)
  have harray11 : array ≠ 11 :=
    hsource array (by simp) 11 (by simp)
  have harray12 : array ≠ 12 :=
    hsource array (by simp) 12 (by simp)
  have harray13 : array ≠ 13 :=
    hsource array (by simp) 13 (by simp)
  have harrayLength10 : arrayLength ≠ 10 :=
    hsource arrayLength (by simp) 10 (by simp)
  have harrayLength11 : arrayLength ≠ 11 :=
    hsource arrayLength (by simp) 11 (by simp)
  have harrayLength12 : arrayLength ≠ 12 :=
    hsource arrayLength (by simp) 12 (by simp)
  have harrayLength13 : arrayLength ≠ 13 :=
    hsource arrayLength (by simp) 13 (by simp)
  simpa [executeInstructionsWithFfi, executeWithFfi, executeInstructions,
    execute, writeRegister, readRegister, nextPc,
    hconfiguration10, hconfiguration11, hconfiguration12, hconfiguration13,
    hconfigurationLength10, hconfigurationLength11,
    hconfigurationLength12, hconfigurationLength13,
    harray10, harray11, harray12, harray13,
    harrayLength10, harrayLength11, harrayLength12, harrayLength13, hzero,
    hzero', Nat.mod_eq_of_lt hservice_bounded]
    using hhost

theorem wordFfiToRiscV_execute_agreement
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width) (wordHandler : FunName → Word width →
      Word width → Word width → Word width → State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (service : Nat) (configurationRegister configurationLengthRegister
      arrayRegister arrayLengthRegister : Fin 32)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hconfiguration : registerOfNat configuration = some configurationRegister)
    (hconfigurationLength : registerOfNat configurationLength =
      some configurationLengthRegister)
    (harray : registerOfNat array = some arrayRegister)
    (harrayLength : registerOfNat arrayLength = some arrayLengthRegister)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configurationRegister, configurationLengthRegister, arrayRegister,
        arrayLengthRegister] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhandler : host service
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister)
      (executeInstructions state
        [.addi 10 configurationRegister (0#width),
         .addi 11 configurationLengthRegister (0#width),
         .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      wordHandler function
        (readRegister state configurationRegister)
        (readRegister state configurationLengthRegister)
        (readRegister state arrayRegister)
        (readRegister state arrayLengthRegister) state) :
    (wordFfiToRiscV context function configuration configurationLength array
      arrayLength).bind (fun code =>
        (executeInstructionsWithFfi host state code).map (fun result =>
          (result, ([] : List (Word width))))) =
      evalWordFfi wordHandler 1 state
        (.ffi function configuration configurationLength array arrayLength ([], [])) := by
  have h10 : registerOfNat 10 = some 10 := by decide
  have h11 : registerOfNat 11 = some 11 := by decide
  have h12 : registerOfNat 12 = some 12 := by decide
  have h13 : registerOfNat 13 = some 13 := by decide
  cases hwordHandler : wordHandler function
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister) state with
  | none =>
      have hhost_none : host service
          (readRegister state configurationRegister)
          (readRegister state configurationLengthRegister)
          (readRegister state arrayRegister)
          (readRegister state arrayLengthRegister)
          (executeInstructions state
            [.addi 10 configurationRegister (0#width),
             .addi 11 configurationLengthRegister (0#width),
             .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
             .addi 14 0 (BitVec.ofNat width service)]) = none := by
        simpa [hwordHandler] using hhandler
      have hexecuted : executeInstructionsWithFfi host state
          [.addi 10 configurationRegister (0#width),
           .addi 11 configurationLengthRegister (0#width),
           .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
           .addi 14 0 (BitVec.ofNat width service), .ecall] = none :=
        executeInstructionsWithFfi_wordFfi_abi host state service
          configurationRegister configurationLengthRegister arrayRegister
          arrayLengthRegister none hservice_bounded hzero hsource hhost_none
      simp [wordFfiToRiscV, hservice, wordRegisterMoves, h10, h11, h12, h13,
        
        hconfiguration, hconfigurationLength, harray, harrayLength,
        evalWordFfi, hwordHandler, hexecuted]
  | some resultState =>
      have hhost_some : host service
          (readRegister state configurationRegister)
          (readRegister state configurationLengthRegister)
          (readRegister state arrayRegister)
          (readRegister state arrayLengthRegister)
          (executeInstructions state
            [.addi 10 configurationRegister (0#width),
             .addi 11 configurationLengthRegister (0#width),
             .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
             .addi 14 0 (BitVec.ofNat width service)]) = some resultState := by
        simpa [hwordHandler] using hhandler
      have hexecuted := executeInstructionsWithFfi_wordFfi_abi host state service
        configurationRegister configurationLengthRegister arrayRegister
        arrayLengthRegister (some resultState) hservice_bounded hzero hsource hhost_some
      simp [wordFfiToRiscV, hservice, wordRegisterMoves, h10, h11, h12, h13,
        
        hconfiguration, hconfigurationLength, harray, harrayLength,
        evalWordFfi, hwordHandler, hexecuted]

/-!
The previous theorem compares the raw FFI selector with the one-step Word
semantics.  This wrapper lifts that agreement through the compiler's
call-aware `WordProg` entry point, making the generated code and the
fuel-bounded handler-aware evaluator share one semantic statement.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_ffi_simulation
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width)
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (service : Nat) (configurationRegister configurationLengthRegister
      arrayRegister arrayLengthRegister : Fin 32)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hconfiguration : registerOfNat configuration = some configurationRegister)
    (hconfigurationLength : registerOfNat configurationLength =
      some configurationLengthRegister)
    (harray : registerOfNat array = some arrayRegister)
    (harrayLength : registerOfNat arrayLength = some arrayLengthRegister)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configurationRegister, configurationLengthRegister, arrayRegister,
        arrayLengthRegister] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhandler : host service
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister)
      (executeInstructions state
        [.addi 10 configurationRegister (0#width),
         .addi 11 configurationLengthRegister (0#width),
         .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      wordHandler function
        (readRegister state configurationRegister)
        (readRegister state configurationLengthRegister)
        (readRegister state arrayRegister)
        (readRegister state arrayLengthRegister) state) :
    (wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := context.services } : WordCallFfiContext width)
      (.ffi function configuration configurationLength array arrayLength ([], []))).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, ([] : List (Word width))))) =
      evalWordFunctionWithCallsAndFfi [] wordHandler 1 state
        (.ffi function configuration configurationLength array arrayLength ([], [])) := by
  simpa [wordFunctionToRiscVWithCallsAndFfi, Option.bind_assoc,
    evalWordFunctionWithCallsAndFfi] using
    (wordFfiToRiscV_execute_agreement context host wordHandler state function
      configuration configurationLength array arrayLength service
      configurationRegister configurationLengthRegister arrayRegister
      arrayLengthRegister hservice hservice_bounded hconfiguration
      hconfigurationLength harray harrayLength hzero hsource hhandler)

/-!
The one-step FFI theorem composes with the compiler's sequencing rule.  A
normal first component contributes code without return values, while the
second component determines the return-register list of the whole sequence.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_seq_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfi context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState) :
    (wordFunctionToRiscVWithCallsAndFfi context (.seq first second)).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, returns))) =
      some (finalState, returns) := by
  simp [wordFunctionToRiscVWithCallsAndFfi, hfirstCompile, hsecondCompile,
    executeInstructionsWithFfi_append, hfirstExec, hsecondExec]

/-!
The uncounted machine agreement is also enough to recover an exact instruction
step count.  This is intentionally phrased at the compiled Word boundary: a
later source-to-Word theorem can supply the semantic agreement hypothesis
without depending on the details of FFI service selection.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_counted_simulation_general
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state finalState : State width)
    (program : WordProg (Word width)) (code : List (Instruction width))
    (returnRegisters : List (Fin 32)) (returnValues : List (Word width))
    (hcompile : wordFunctionToRiscVWithCallsAndFfi context program =
      some (code, returnRegisters))
    (hsemantic :
      (wordFunctionToRiscVWithCallsAndFfi context program).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, returnValues))) =
        some (finalState, returnValues)) :
    executeInstructionsWithFfiCounted host state code =
      some (finalState, code.length) := by
  have hrun : executeInstructionsWithFfi host state code = some finalState := by
    cases hexecute : executeInstructionsWithFfi host state code with
    | none =>
        simp [hcompile, hexecute] at hsemantic
    | some actualState =>
        have hresult :
            (actualState, returnValues) = (finalState, returnValues) := by
          simpa [hcompile, hexecute] using hsemantic
        cases hresult
        rfl
  rw [executeInstructionsWithFfiCounted_spec]
  simp [hrun]

/-! The loop-aware selector has the same machine-count boundary.  Keeping the
    theorem at this compiler entrypoint is useful to callers that retain
    resolved break/continue control in their source witness. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_counted_simulation_general
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state finalState : State width)
    (program : WordProg (Word width)) (code : List (Instruction width))
    (returnRegisters : List (Fin 32)) (returnValues : List (Word width))
    (hcompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context program =
      some (code, returnRegisters))
    (hsemantic :
      (wordFunctionToRiscVWithCallsAndFfiAndLoops context program).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, returnValues))) =
        some (finalState, returnValues)) :
    executeInstructionsWithFfiCounted host state code =
      some (finalState, code.length) := by
  have hrun : executeInstructionsWithFfi host state code = some finalState := by
    cases hexecute : executeInstructionsWithFfi host state code with
    | none =>
        simp [hcompile, hexecute] at hsemantic
    | some actualState =>
        have hresult :
            (actualState, returnValues) = (finalState, returnValues) := by
          simpa [hcompile, hexecute] using hsemantic
        cases hresult
        rfl
  rw [executeInstructionsWithFfiCounted_spec]
  simp [hrun]

theorem wordFunctionToRiscVWithCallsAndFfi_counted_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state finalState : State width)
    (program : WordProg (Word width)) (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCallsAndFfi context program =
      some (code, []))
    (hsemantic :
      (wordFunctionToRiscVWithCallsAndFfi context program).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, ([] : List (Word width))))) =
        some (finalState, [])) :
    executeInstructionsWithFfiCounted host state code =
      some (finalState, code.length) := by
  exact wordFunctionToRiscVWithCallsAndFfi_counted_simulation_general context host
    state finalState program code [] [] hcompile hsemantic

/-!
The machine sequencing theorem and the evaluator sequencing theorem above are
usually consumed together by a pass-level correctness proof.  This combined
contract keeps that composition explicit: a normal first component, followed
by a second component, has the same final state and return values in both the
FFI-aware Word evaluator and the generated RISC-V instruction stream.

The hypotheses deliberately expose the component boundaries.  In particular,
the theorem does not assume that either component is straight-line code; the
component compiler and execution witnesses may already include calls, FFI,
or resolved loop control.
-/
theorem wordFunctionToRiscVWithCallsAndFfi_seq_complete_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (host : WordFfiHost width)
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32)) (values : List (Word width))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfi context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState)
    (hfirstEval : evalWordFunctionWithCallsAndFfi functions handler fuel state first =
      some (firstState, []))
    (hsecondEval : evalWordFunctionWithCallsAndFfi functions handler fuel firstState second =
      some (finalState, values)) :
    ((wordFunctionToRiscVWithCallsAndFfi context (.seq first second)).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, returns))) =
      some (finalState, returns)) ∧
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.seq first second) = some (finalState, values) := by
  constructor
  · exact wordFunctionToRiscVWithCallsAndFfi_seq_simulation context host state
      firstState finalState first second firstCode secondCode returns
      hfirstCompile hsecondCompile hfirstExec hsecondExec
  · exact evalWordFunctionWithCallsAndFfi_seq_normal functions handler fuel state
      firstState finalState first second values hfirstEval hsecondEval

/-! The preceding sequencing contract can be lifted to the counted machine
    runner. The selector witness remains explicit, so callers can use this
    theorem after a pass has established the exact concatenated code shape. -/
theorem wordFunctionToRiscVWithCallsAndFfi_seq_counted_complete_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (host : WordFfiHost width)
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32)) (values : List (Word width))
    (hseqCompile : wordFunctionToRiscVWithCallsAndFfi context
      (.seq first second) = some (firstCode ++ secondCode, returns))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfi context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState)
    (hfirstEval : evalWordFunctionWithCallsAndFfi functions handler fuel state first =
      some (firstState, []))
    (hsecondEval : evalWordFunctionWithCallsAndFfi functions handler fuel firstState second =
      some (finalState, values)) :
    executeInstructionsWithFfiCounted host state (firstCode ++ secondCode) =
      some (finalState, (firstCode ++ secondCode).length) ∧
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.seq first second) = some (finalState, values) := by
  have hcomplete := wordFunctionToRiscVWithCallsAndFfi_seq_complete_simulation
    context functions host handler fuel state firstState finalState first second
    firstCode secondCode returns values hfirstCompile hsecondCompile hfirstExec
    hsecondExec hfirstEval hsecondEval
  have hrun : executeInstructionsWithFfi host state (firstCode ++ secondCode) =
      some finalState := by
    have hprojection := congrArg (Option.map Prod.fst) hcomplete.1
    simpa [hseqCompile] using hprojection
  have hsemantic :
      (wordFunctionToRiscVWithCallsAndFfi context (.seq first second)).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, values))) =
        some (finalState, values) := by
    simp [hseqCompile, hrun]
  have hcount := wordFunctionToRiscVWithCallsAndFfi_counted_simulation_general
    context host state finalState (.seq first second) (firstCode ++ secondCode)
    returns values hseqCompile hsemantic
  exact ⟨hcount, hcomplete.2⟩

theorem wordControlInstructions_append_of_success
    [NeZero width] (first second : List (WordControlInstruction width))
    (firstCode secondCode : List (Instruction width))
    (hfirst : wordControlInstructions first = some firstCode)
    (hsecond : wordControlInstructions second = some secondCode) :
    wordControlInstructions (first ++ second) = some (firstCode ++ secondCode) := by
  induction first generalizing firstCode with
  | nil =>
      simp only [List.nil_append, wordControlInstructions] at hfirst ⊢
      cases hfirst
      simpa using hsecond
  | cons instruction first ih =>
      cases instruction with
      | instruction instruction =>
          simp only [wordControlInstructions] at hfirst ⊢
          cases htail : wordControlInstructions first with
          | none => simp [htail] at hfirst
          | some tailCode =>
              have hcode : instruction :: tailCode = firstCode := by
                simpa [htail] using hfirst
              subst firstCode
              have happend := ih (firstCode := tailCode) htail
              simp [List.cons_append, wordControlInstructions, happend]
      | breakJump => simp [wordControlInstructions] at hfirst
      | continueJump => simp [wordControlInstructions] at hfirst

/-!
The same sequencing boundary remains valid after enabling loop lowering.
The loop-aware selector may resolve control markers inside either component,
but once those components have produced ordinary instruction lists their
machine effects still compose by list append.  Keeping this theorem separate
from the unclocked evaluator lets loop and handler proofs use the exact
compiled code without re-proving the selector's sequencing equation.
-/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_seq_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (host : WordFfiHost width) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState) :
    (wordFunctionToRiscVWithCallsAndFfiAndLoops context (.seq first second)).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, returns))) =
      some (finalState, returns) := by
  cases hfirstAux : wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context first with
  | none =>
      simp [wordFunctionToRiscVWithCallsAndFfiAndLoops, hfirstAux] at hfirstCompile
  | some firstResult =>
      cases firstResult with
      | mk firstControl firstReturns =>
          have hfirstBind :
              (wordControlInstructions firstControl).bind
                (fun code => some (code, firstReturns)) =
                some (firstCode, ([] : List (Fin 32))) := by
            simpa [wordFunctionToRiscVWithCallsAndFfiAndLoops,
              hfirstAux] using hfirstCompile
          cases firstReturns with
          | nil =>
              cases hsecondAux :
                  wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context second with
              | none =>
                  simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
                    hsecondAux] at hsecondCompile
              | some secondResult =>
                  cases secondResult with
                  | mk secondControl secondReturns =>
                      cases hfirstControlLowering :
                          wordControlInstructions firstControl with
                      | none => simp [hfirstControlLowering] at hfirstBind
                      | some loweredFirstCode =>
                          have hfirstPair :
                              (loweredFirstCode, ([] : List (Fin 32))) =
                                (firstCode, []) := by
                            simpa [hfirstControlLowering] using hfirstBind
                          have hfirstControl : loweredFirstCode = firstCode :=
                            congrArg Prod.fst hfirstPair
                          have hsecondBind :
                              (wordControlInstructions secondControl).bind
                                (fun code => some (code, secondReturns)) =
                                some (secondCode, returns) := by
                            simpa [wordFunctionToRiscVWithCallsAndFfiAndLoops,
                              hsecondAux] using hsecondCompile
                          cases hsecondControlLowering :
                              wordControlInstructions secondControl with
                          | none => simp [hsecondControlLowering] at hsecondBind
                          | some loweredSecondCode =>
                              have hsecondPair :
                                  (loweredSecondCode, secondReturns) =
                                    (secondCode, returns) := by
                                simpa [hsecondControlLowering] using hsecondBind
                              have hsecondControl : loweredSecondCode = secondCode :=
                                congrArg Prod.fst hsecondPair
                              have hreturns : secondReturns = returns :=
                                congrArg Prod.snd hsecondPair
                              subst loweredFirstCode
                              subst loweredSecondCode
                              subst secondReturns
                              have hfirstControl' :
                                  wordControlInstructions firstControl = some firstCode :=
                                hfirstControlLowering ▸ rfl
                              have hsecondControl' :
                                  wordControlInstructions secondControl = some secondCode :=
                                hsecondControlLowering ▸ rfl
                              have hcombined := wordControlInstructions_append_of_success
                                firstControl secondControl firstCode secondCode
                                hfirstControl' hsecondControl'
                              have hseqCompile :
                                  wordFunctionToRiscVWithCallsAndFfiAndLoops context
                                      (.seq first second) =
                                    some (firstCode ++ secondCode, returns) := by
                                simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
                                  wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
                                  hfirstAux, hsecondAux, hcombined]
                              rw [hseqCompile]
                              simp [executeInstructionsWithFfi_append,
                                hfirstExec, hsecondExec]
          | cons firstReturn firstReturns =>
              cases hfirstControlLowering :
                  wordControlInstructions firstControl with
              | none => simp [hfirstControlLowering] at hfirstBind
              | some loweredFirstCode =>
                  simp [hfirstControlLowering] at hfirstBind

/-! The counted machine contract composes through the loop-aware selector as
    well.  The control-marker proof above recovers the exact concatenated
    instruction list; the generic counted contract then supplies the machine
    step count for that list. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_seq_counted_complete_simulation
    [NeZero width] (context : WordCallFfiContext width)
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (host : WordFfiHost width)
    (handler : FunName → Word width → Word width → Word width →
      Word width → State width → Option (State width))
    (fuel : Nat) (state firstState finalState : State width)
    (first second : WordProg (Word width))
    (firstCode secondCode : List (Instruction width))
    (returns : List (Fin 32)) (values : List (Word width))
    (hseqCompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context
      (.seq first second) = some (firstCode ++ secondCode, returns))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context first =
      some (firstCode, []))
    (hsecondCompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context second =
      some (secondCode, returns))
    (hfirstExec : executeInstructionsWithFfi host state firstCode =
      some firstState)
    (hsecondExec : executeInstructionsWithFfi host firstState secondCode =
      some finalState)
    (hfirstEval : evalWordFunctionWithCallsAndFfi functions handler fuel state first =
      some (firstState, []))
    (hsecondEval : evalWordFunctionWithCallsAndFfi functions handler fuel firstState second =
      some (finalState, values)) :
    executeInstructionsWithFfiCounted host state (firstCode ++ secondCode) =
      some (finalState, (firstCode ++ secondCode).length) ∧
    evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
      (.seq first second) = some (finalState, values) := by
  have hmachine := wordFunctionToRiscVWithCallsAndFfiAndLoops_seq_simulation
    context host state firstState finalState first second firstCode secondCode
    returns hfirstCompile hsecondCompile hfirstExec hsecondExec
  have heval := evalWordFunctionWithCallsAndFfi_seq_normal
    functions handler fuel state firstState finalState first second values
    hfirstEval hsecondEval
  have hcomplete :
      ((wordFunctionToRiscVWithCallsAndFfiAndLoops context (.seq first second)).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, returns))) =
        some (finalState, returns)) ∧
      evalWordFunctionWithCallsAndFfi functions handler (fuel + 1) state
        (.seq first second) = some (finalState, values) :=
    ⟨hmachine, heval⟩
  have hrun : executeInstructionsWithFfi host state (firstCode ++ secondCode) =
      some finalState := by
    have hprojection := congrArg (Option.map Prod.fst) hcomplete.1
    simpa [hseqCompile] using hprojection
  have hsemantic :
      (wordFunctionToRiscVWithCallsAndFfiAndLoops context (.seq first second)).bind
          (fun result =>
            (executeInstructionsWithFfi host state result.1).map
              (fun final => (final, values))) =
        some (finalState, values) := by
    simp [hseqCompile, hrun]
  have hcount := wordFunctionToRiscVWithCallsAndFfiAndLoops_counted_simulation_general
    context host state finalState (.seq first second) (firstCode ++ secondCode)
    returns values hseqCompile hsemantic
  exact ⟨hcount, hcomplete.2⟩

end Flapjack.RiscV
