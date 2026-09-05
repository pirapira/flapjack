# Flapjack: Pancake Lean port plan

## Goal

Build a usable Lean 4 development of Pancake, including its executable
compiler pipeline and compiler-correctness theorems. The CakeML checkout in
`cakeml` is the reference implementation and remains useful for cross-checking
definitions, pass ordering, examples, and proof obligations.

## Principles

- Keep the Lean AST close to CakeML's `panLang`/`crepLang`/`loopLang` syntax so
  translation and theorem statements can be compared directly.
- Preserve polymorphism over machine-word values at the syntax boundary; make
  word width and target configuration explicit in later layers.
- Port executable definitions first, then state invariants and correctness
  proofs for each pass. Every ported layer should have small computation tests
  before its proof interface is expanded.
- Keep the CakeML submodule untouched from the parent project. HOL builds can
  be run in the submodule independently with Holmake.

## Stages

1. **Project and syntax foundation**
   - Initialize Lake and pin the Lean toolchain.
   - Port the core declarations from `cakeml/pancake/panLangScript.sml`.
   - Port structural helpers such as shape size and nested sequencing.
   - Add Lean examples/tests for constructors and helper behavior.

2. **Static data and front-end support**
   - Port shape well-formedness, struct contexts, declarations, and the
     Pancake static-checker result/error types.
   - Port parser-facing syntax only after the AST and diagnostics are stable.
   - Establish executable validation examples corresponding to CakeML's
     `static_checker` examples.

3. **Semantics**
   - Define a deterministic big-step/trace semantics for Pancake, including
     memory, calls, exceptions, loops, and foreign calls.
   - State and prove preservation of well-formedness and basic determinism.

4. **Compiler passes**
   - Port `pan_to_crep`, then the simplification/struct/global passes.
   - Port `crep_to_loop`, loop optimisations, liveness, and `loop_to_word`.
   - For each pass, add a simulation relation and a correctness theorem before
     composing it into the full compiler.

5. **Target and end-to-end correctness**
   - Port the word-level/target interface and one concrete backend first.
   - Use `/home/zksecurity/HOL/examples/l3-machine-code/riscv/model/riscv.sml`
     as the RISC-V architectural reference; copy `/home/zksecurity/HOL/COPYRIGHT`
     into the Lean RISC-V model subdirectory when that port starts.
   - Connect the compiled result to a Lean execution model and prove the
     end-to-end compiler-correctness statement.
   - Add regression programs and differential checks against CakeML/HOL where
     practical.

## Progress

- [x] Initialize Lake with a pinned Lean 4.33.1 toolchain.
- [x] Port the core `panLang` syntax, shape sizing, and nested sequencing.
- [x] Port nested-recursion local/global expression variable-use helpers.
- [x] Port static-checker data types, structural shape validation, and
  declaration-level shape validation.
- [x] Add a shape-aware executable checker for core expressions and
  diagnostics.
- [x] Check scoped tail/handler-free calls and local return destinations,
  including recursive argument-expression shape matching.
- [x] Port the Crepe IR and executable expression lowering used by
  `pan_to_crep`.
- [x] Port core structured statement lowering and initial pass equations.
- [x] Add parameter-slot allocation and top-level function/declaration
  assembly for the Pancake-to-Crepe pass.
- [x] Materialize primitive arguments and multi-word store/exception payloads
  through fresh Crepe locals.
- [x] Begin the RISC-V target-model port with HOL-derived architectural
  vocabulary, parameterized words, register/memory primitives, and alignment
  traps; preserve the HOL copyright notice in `Flapjack/RiscV/COPYRIGHT`.
- [x] Add executable `ADD`/`ADDI` transitions with PC-advance and
  zero-register preservation theorems.
- [x] Port HOL's signed `LB`/`LH` load value paths alongside the existing
  unsigned byte/halfword operations, with destination-register theorems.
- [x] Port HOL's signed `SLT`/`SLTI` integer comparison value paths and prove
  their destination-register behavior, including x0 handling.
- [x] Add executable deterministic semantics and preservation theorems for
  the supported constant/return/sequence fragment, including scalar local
  assignment state updates.
- [x] Add local-plus-memory semantics and a store/load preservation theorem
  for the scalar compiler fragment.
- [x] Extend the initial lowering with handler-free calls, local return
  destinations, declaration calls, and mapped exceptions.
- [x] Lower calls with known exception handlers to Crepe continuation metadata
  and compile the handler body.
- [x] Lower foreign calls and shared-memory operations through explicit Crepe
  temporaries and memory-operation mappings.
- [x] Port the Loop intermediate-language vocabulary and begin Crepe-to-Loop
  lowering, with structural expression preservation and explicit unsupported
  cases.
- [x] Port Loop variable-use, assigned-variable, and accumulated-variable
  analyses as executable list-based prerequisites for liveness.
- [x] Port the temporary-threaded Crepe-to-Loop expression and program
  equations for materialized loads, comparisons, memory, control flow,
  calls, exceptions, returns, shared memory, and FFI.
- [x] Add the initial Word IR and Loop-to-Word lowering for register mapping,
  expressions, memory instructions, loops, calls, returns, and FFI.
- [x] Port the HOL `pan_simp` sequence-association and tail-call normalization
  pass, including recursive call-handler traversal.
- [x] Port the core `pan_structs` named-shape, field-reordering, expression,
  statement, and declaration transformations.
- [x] Port the context-sensitive `pan_globals` expression and statement core,
  including heap-relative global loads/stores and adjusted `TopAddr`.
- [x] Add global declaration address collection and explicit initializer
  programs for composing the global pass with later compiler stages.
- [x] Compose the ported front-end, global, Crepe, Loop, and Word passes in an
  executable pipeline that exposes every intermediate artifact.
- [x] Add a return-aware RISC-V function artifact and evaluator for the
  straight-line Word assignment/return fragment.
- [x] Add a partial Word-to-RISC-V instruction selector for constants, moves,
  and the register-register ADD/SUB/AND/OR/XOR fragment, with a straight-line
  semantic soundness theorem.
- [x] Make the RISC-V x0 invariant explicit and prove that the instruction
  transition preserves it.
- [x] Connect the composed Word pipeline to a typed, option-valued RISC-V
  function artifact stage for the currently supported straight-line fragment.
- [x] Port byte load/store transitions from the HOL RISC-V model and connect
  the Word load8/store8 operations to them with evaluator agreement.
- [x] Add little-endian 32-bit load/store transitions and connect the Word
  load32/store32 operations to them with evaluator agreement.
- [x] Add full-word register-based store lowering and prove its evaluator
  agreement with the RISC-V byte-memory fold.
- [x] Add declaration-level static checking: structure discovery, global and
  exception environments, function headers, duplicate checks, and missing or
  wrongly shaped returns.
- [x] Extend Pancake/Crepe executable semantics to store32/storeByte and prove
  preservation for constant store-then-load programs.
- [x] Exercise the concrete composed compiler from a Pancake `main` through
  the option-valued RISC-V artifact boundary.
- [x] Integrate static checking into checked compiler entry points that return
  diagnostics instead of compiling malformed declaration lists.
- [x] Extend the RISC-V backend with full-word byte-fold memory operations and
  prove evaluator agreement for register-based Word stores.
- [x] Port equality and inequality branch instructions from the HOL RISC-V
  vocabulary and prove their conditional PC transitions.
- [x] Match HOL `pan_to_crep` for `BytesInWord` and alias-sensitive local
  assignments, including regression tests for both cases.
- [x] Add fuel-bounded conditional and sequencing semantics for Pancake and
  Crepe and prove preservation for a constant conditional program.
- [x] Port the RISC-V low-word multiplication path for HOL `CrepOp.mul` and
  `LoopArith.longMul`, with intermediate and end-to-end tests.
- [x] Port RISC-V register shifts (`SLL`, `SRL`, and `SRA`) with masked shift
  amounts, plus the HOL scratch-register lowering for `ROR`.
- [x] Extend Pancake/Crepe executable expression semantics with `PanOp.mul` and
  prove constant multiplication preservation through `pan_to_crep`.
- [x] Add a fuel-bounded Loop state/control-result evaluator for assignments,
  memory, returns, break/continue, conditionals, and loop execution.
- [x] Prove the first Crepe-to-Loop semantic bridge for constant return
  lowering through the generated temporary assignment.
- [x] Extend that bridge through Crepe `mul`/Loop `longMul` expansion and
  preserve the returned product.
- [x] Prove RISC-V instruction-selection and evaluator agreement for the
  emitted constant-return artifact.
- [x] Lower register-based equality and inequality conditionals to RISC-V,
  including generated branch offsets and a PC-aware code executor.
- [x] Prove concrete taken and fall-through conditional execution paths for
  the generated RISC-V artifact under the fixed-width x0 invariant.
- [x] Connect immediate-zero Word conditions to RISC-V x0 and test the
  resulting conditional function artifact.
- [x] Port unsigned `Lower`/`NotLower` Word conditions to RISC-V `BLTU`/`BGEU`
  and prove their PC transitions.
- [x] Port signed `Less`/`NotLess` Word conditions to RISC-V `BLT`/`BGE` with
  explicit two's-complement ordering and concrete execution proofs.
- [x] Port `Test`/`NotTest` Word conditions through an `AND`/x0 sequence,
  with an explicit dead-condition-register contract and execution proofs.
- [x] Lower Loop-to-Word `Tick` to an architectural `ADDI x0,x0,0` so
  generated conditional function artifacts can cross the RISC-V boundary.
- [x] Lower function-level conditionals with recursively compiled return
  branches, requiring both branches to expose the same return-register layout.
- [x] Preserve terminal function returns when compiling or evaluating a
  sequence with unreachable trailing code.
- [x] Add the pipeline’s initial register context, mapping Loop slots to
  RISC-V registers from x2 and remapping parameter metadata consistently.
- [x] Add an executable RISC-V function harness that initializes parameter
  registers and collects declared return registers, with an `ADD` proof.
- [x] Add a Word-level FFI evaluator with an explicit host-handler boundary,
  its single-call semantic equation, and a concrete handler regression.
- [x] Generalize the combined Loop-to-Word FFI simulation boundary to any
  positive fuel budget, so it composes with fuel-bounded call-aware proofs.
- [x] Add the normal-path combined sequence simulation rule and exercise an
  FFI followed by a resumed Word tick continuation.
- [x] Add Word control-result semantics for handler-aware calls, including
  normal, returned, and raised paths with handler resumption.
- [x] Add homogeneous BitVec shift instances for the Word semantic bridge.
- [x] Prove the first Loop-to-Word state-observation agreements for constant
  and register-register ADD assignments, with the RISC-V x0 invariant explicit.
- [x] Make the Loop-to-Word register observation context-parametric for
  mapped constant and register-register ADD assignments.
- [x] Prove a generic Loop-to-Word register-observation agreement for
  context-mapped `LongMul`.
- [x] Exercise that harness on an artifact produced by the composed
  Pancake-to-RISC-V pipeline for a two-parameter addition function.
- [x] Connect Word full-word stores to function artifacts and prove a
  store/load function through the RISC-V byte-memory model.
- [x] Port the direct RISC-V `JAL` PC-transfer/link-register transition as
  the machine-model foundation for later function calls.
- [x] Port the direct RISC-V `JALR` register-target transition, including
  link-register behavior and the architectural low-bit clear.
- [x] Add a return-address-aware RISC-V function runner and execute a callee
  returning through `JALR x0, ra, 0`.
- [x] Add the first call-aware Loop semantic bridge: function lookup,
  argument binding, return assignment, tail-call propagation, and handler
  entry for top-level calls.
- [x] Extend call-aware Loop evaluation through nested and recursive function
  bodies with fuel decreasing across the call graph.
- [x] Thread call-aware evaluation through Loop repetition and break/continue
  handling.
- [x] Add Loop shared-memory load/store semantics for all modeled widths,
  using the executable memory state.
- [x] Add an explicit fuel-bounded Loop FFI environment bridge with evaluated
  word arguments and host-controlled state updates.
- [x] Add a RISC-V ECALL FFI ABI boundary with service-name resolution,
  argument marshalling, option-valued host execution, and executable
  instruction-level regressions.
- [x] Port the StackLang handler/FFI carriers and initial `word_to_stack`
  call, raise, and foreign-call boundary equations, with a local HOL
  copyright notice and structural regressions.
- [x] Port the core StackLang-to-LabLang flattening pass for calls, handlers,
  loops, exceptions, labels, and FFI, with executable label-counter
  regressions and a local HOL copyright notice.
- [x] Add a concrete LabLang-to-RISC-V resolver for local label positions,
  symbolic jumps, conditional branches, and ECALL service names, with
  explicit failure for unsupported target operations and executable tests.
- [x] Extend LabLang linking across multiple sections with byte-base layout,
  section-qualified labels, and an executable cross-section jump regression.
- [x] Port the core StackLang-to-LabLang flattening pass for calls, handlers,
  loops, exceptions, labels, and FFI, with executable label-counter
  regressions and a local HOL copyright notice.
- [x] Add a unified fuel-bounded Loop evaluator that composes function calls
  and host-controlled FFI effects in one control-result semantics.
- [x] Preserve a static-check success while diagnosing unreachable sequence
  tails after a definite function exit.
- [x] Add a library-level end-to-end correctness theorem for the composed
  RV64 Pancake-to-RISC-V addition pipeline, parameterized over inputs.
- [x] Add a composed RV64 Pancake-to-RISC-V multiplication artifact shape and
  executable correctness theorem, including context-aware LongMul operands.
- [x] Add a fuel-bounded Word function-table evaluator with nested calls,
  return-register assignment, tail calls, and memory-state propagation.
- [x] Add the first RISC-V call-sequence selector and execute its linked
  argument-move, `JALR`, return, and result-move convention.
- [x] Add RISC-V function-artifact linking by byte length and resolve Word
  call labels to linked entry addresses.
- [x] Add recursive Word call instruction selection for handler-free calls,
  using linked callee signatures and the explicit call convention.
- [x] Add a two-pass Word function linker that derives return signatures,
  computes byte-addressed function layout, resolves call labels, and
  re-emits the final linked artifacts.
- [x] Relate the generated linked call artifact to its executable image and
  prove execution of that generated image, rather than only a hand-written
  instruction list.
- [x] Give ordinary linked calls a stack-preserved `x1` link register and
  reserve `x30` as the downward-growing stack pointer; lower no-destination
  calls as true tail calls.
- [x] Expose linked RISC-V function artifacts directly from the composed
  pipeline result.
- [x] Expose the call-aware two-pass linked artifacts alongside the original
  straight-line artifact table, preserving the first correctness theorem.
- [x] Port complete program checking, context transitions, and diagnostics for
  the current AST, including declaration environments, missing returns,
  unreachable-tail warnings, and location annotations. The diagnostic surface
  remains intentionally smaller than CakeML's rich structured messages.
- [x] Add a fuel-bounded, structurally recursive loop evaluator for the
  currently modeled Loop fragment.
- [x] Extend the Loop evaluator with executable word division and preserve
  the result through a fuel-bounded arithmetic-program regression.
- [x] Port unsigned RISC-V `DIVU`/`REMU`, including their divide-by-zero
  behavior, and select `DIVU` for Word division.
- [x] Add immediate RISC-V bitwise transitions (`ANDI`, `ORI`, `XORI`) and
  select them for normalized Word expressions, with subtract-immediate via
  `ADDI`.
- [x] Add immediate RISC-V shift transitions (`SLLI`, `SRLI`, `SRAI`) and
  select them for normalized Word shift expressions.
- [x] Port the HOL RISC-V rotate-right lowering as a scratch-register
  instruction sequence, including immediate and register-count forms and the
  reserved `x31` alias contract.
- [x] Extend Word-level ROR evaluation and prove immediate ROR compiler
  agreement at the destination-register observation boundary, including
  immediate shift-count normalization.
- [x] Lower nonzero immediate RISC-V conditional operands using HOL-aligned
  `ORI`/`ANDI` scratch materialization, with an explicit `x31` condition guard.
- [x] Thread the immediate-condition and multi-instruction expression
  lowering through the call-aware RISC-V function selector.
- [x] Thread normalized register and offset-addressed memory lowering through
  the call-aware RISC-V function selector.
- [x] Lower Word expression-level full-word loads through the reserved
  address scratch register, with evaluator agreement and pipeline coverage.
- [x] Port the HOL RISC-V `AddCarry` lowering through Word instruction
  selection and execution, including its reserved `x31` scratch contract.
- [x] Keep Loop-to-Word `AddCarry` as a five-register operation until
  instruction selection, and prove a structured primitive through the
  call-linked RISC-V artifact without clobbering the `x1` link register.
- [x] Add an executable Option-valued Word allocator boundary that preserves
  existing low-numbered mappings and rejects reserved-register exhaustion.
- [x] Add an executable undirected clash-edge checker and
  preferred-register-aware greedy colouring boundary for Word variables.
- [x] Add straight-line Word liveness and clash construction feeding the
  executable colouring boundary.
- [x] Add straight-line SSA renaming for Word writes and reads, including
  multi-result arithmetic instructions.
- [x] Extend straight-line Word SSA through memory operations, `locValue`,
  returns, exceptions, FFI arguments, and handler-free call metadata, while
  matching liveness reads and writes to those data-flow conventions.
- [x] Extend Word SSA through handler-bearing calls, recursively renaming the
  handler body, reconciling its normal continuation with the call path, and
  advancing fresh names across both paths; cover the transformation with an
  executable Word control-result regression.
- [x] Feed actual WordProg sequencing into backwards liveness and conservative
  control-flow clash construction.
- [x] Expose a program-analysis-driven Word pipeline allocation boundary for
  straight-line and conservatively analysed control-flow programs.
- [x] Add branch-aware Word SSA version reconciliation and tighten program
  clash analysis to write/live interference for the supported control-flow
  fragment.
- [x] Add CakeML-aligned loop SSA setup for Word live-in/live-out names, with
  refreshed loop frames and explicit back-edge plus `break`/`continue`
  reconciliation moves.
- [x] Port recursive Word register-colouring over expressions, instructions,
  nested handlers, loops, and call metadata, and expose the coloured pipeline
  boundary.
- [x] Add an explicit spill-aware Word allocation result with fresh stack-slot
  assignment and a register/spill clash-validation contract; stack access
  rewriting remains a separate backend pass.
- [x] Expose an SSA-driven spill allocation boundary that derives spill
  locations from the renamed Word program and its analysed clash graph.
- [ ] Port CakeML's full SSA/clash-colouring Word allocator and its spill-aware
  RISC-V contracts before claiming general call-aware allocation correctness.
- [x] Expose witness-level allocator contracts showing every successfully
  coloured SSA slot maps to an allocatable RISC-V register.
- [x] Prove spill-aware allocation assigns every requested slot a concrete
  register or stack location.
- [x] Port the first CakeML `word_to_stack` spill-move boundary, including all
  register/stack source and destination combinations.
- [x] Give generated spill moves an executable StackLang semantics and prove
  source-value preservation under the reserved-scratch contract.
- [x] Lower spilled Word load/store instructions through independent address
  and data scratch registers in the StackLang boundary.
- [x] Lower spilled Word division operands and destinations through the
  StackLang arithmetic boundary.
- [x] Extend the Word-to-Stack boundary through conditions, loops, returns,
  calls, exception handlers, special stores, and FFI operations.
- [x] Add concrete `Nat` Word-to-Stack expression lowering for constants,
  register/stack atoms, binary operations, loads, stores, and stack-backed
  destinations, with separate value/address scratch registers.
- [x] Add executable concrete StackLang semantics for registers, frame slots,
  stores, and abstract full-word memory, with a constant-assignment
  preservation theorem.
- [x] Add a StackLang shift carrier and lower register/immediate Word shifts,
  including spilled operands, through the concrete Nat expression compiler.
- [x] Preserve StackLang arithmetic and shifts through LabLang and lower them
  to executable RISC-V instructions, including sized rotate-right expansion.
- [x] Preserve `ShMemOp` as a distinct StackLang operation through LabLang
  and the RISC-V shared-memory selector.
- [x] Port the HOL RISC-V `LongMul` lowering with executable unsigned high-half
  multiplication (`MULHU`) followed by low-half multiplication (`MUL`),
  including the target's high-destination/source non-aliasing precondition.
- [x] Port register-addressed and simple offset-addressed `WordProg.shareInst`
  memory lowering for all currently modeled HOL word load/store operators,
  including evaluator and call-aware selector coverage.
- [x] Reuse the normalized address materialization for ordinary `WordProg.store`
  operations, covering the store form emitted by global rewriting.
- [x] Lower `WordProg.locValue` through the plain and call-aware RISC-V
  selectors, with executable evaluator agreement.
- [x] Port unsigned RISC-V halfword (`LHU`/`SH`) memory operations through the
  model, Word IR, selector, evaluator, and executable round-trip regression.
- [x] Port CakeML flat-memory byte and aligned 32-bit load/store operations
  over RISC-V word cells, with little-endian and alignment regressions.
- [x] Prove model-level register agreements for unsigned RISC-V division and
  remainder, including the HOL/RISC-V zero-divisor results.
- [x] Prove the AddCarry lowering preserves non-result registers outside its
  two destinations and x31 scratch register.
- [x] Generalize the AddCarry result theorem to arbitrary allocator-selected
  registers under explicit destination/source/scratch non-alias conditions.
- [x] Prove a mapped Loop-to-Word AddCarry agreement under explicit register
  value, destination non-alias, and allocator scratch contracts.
- [x] Lift the Loop no-memory-write projection invariant from one step to
  arbitrary fuel, including sequencing, conditionals, loop repetition, and
  control results.
- [ ] Prove the complete Loop state-preservation theorem, including the
  remaining operations and control-flow invariants.
- [x] Add the terminal return control-result bridge, including mapped state
  preservation and equality of Loop and Word returned value lists.
- [x] Add the terminal raise control-result bridge, including mapped state
  preservation and equality of Loop and Word raised exception values.
- [x] Prove that compiler-generated RISC-V ticks preserve the mapped-local
  relation needed by conditional and loop simulations.
- [x] Prove conditional branch simulation for fuel-2 Loop programs, including
  the compiler-generated post-conditional tick.
- [x] Add fuel-bounded Word loop execution with explicit break and continue
  control results, plus basic loop-control regression theorems.
- [x] Exercise the actual Loop-to-Word loop lowering through the Word loop
  evaluator, including its generated entry and exit ticks.
- [x] Add layout-aware RISC-V lowering for Word loops, resolving generated
  break and continue jumps and wiring it into the default pipeline.
- [x] Extend call-aware RISC-V lowering and linked return-signature derivation
  to retain loop-containing Word functions.
- [x] Execute a lowered RISC-V loop with a generated break jump through the
  architectural code runner.
- [x] Add an end-to-end source `while` regression through Loop/Word loop
  lowering and RISC-V architectural execution.
- [x] Add an end-to-end source full-word store/load regression through the
  composed pipeline and RISC-V byte-memory execution.
- [x] Promote the composed full-word store/load regression to a library-level
  source-memory versus compiled-RISC-V correctness theorem.
- [x] Prove generic fuel-inductive Loop/Word repeat preservation for normal,
  break, and continue control results.
- [x] Compose repeat preservation with the generated entry/exit ticks and prove
  the outer Loop-to-Word loop simulation rule.
- [x] Prove the one-step global-state projection invariant for every Loop
  constructor under the no-global-writes syntactic side condition.
- [x] Lift the global-state projection invariant to arbitrary fuel, including
  sequence, conditional, loop-repeat, and control-result cases.
- [x] Derive the direct successful-evaluation global-state corollary used by
  downstream Loop result-state proofs.
- [x] Prove the first source-to-Crepe-to-Loop semantic bridge for compiled
  constant returns using the executable Loop evaluator.
- [x] Establish reusable Loop state-transition lemmas for the modeled
  assignment, load/store (including byte and 32-bit forms), shared-memory,
  `locValue`, global, return, and control-result cases.
- [x] Isolate successful option-bind result-state invariants for use in the
  fuel-bounded Loop preservation induction.
- [x] Add context-mapped Loop-to-Word register agreements for assignments
  and read-only 32-bit loads, plus the low-byte memory observation for
  `store32`, with explicit byte-fold memory premises.
- [x] Prove mapped-local state preservation for compiled Loop/RISC-V `load32`
  and `store32`, including source-memory and architectural-word observations.
- [x] Prove mapped-local state preservation for compiled byte loads and stores,
  including zero-extension and preservation of all non-destination locals.
- [x] Prove mapped-local preservation for structured shared-memory `load8` and
  `store8` lowering through the emitted `shareInst` operations.
- [x] Prove mapped-local preservation for structured shared-memory `load16` and
  `store16` lowering through the emitted `shareInst` operations.
- [x] Prove mapped-local preservation for structured shared-memory full-word
  `load` and `store` lowering, including register preservation through the
  byte-fold word store.
- [x] Prove mapped-local preservation for ordinary constant-address `store`
  lowering, with the RISC-V x31 address-materialization scratch contract.
- [x] Generalize the context-mapped Loop-to-Word assignment agreement to all
  register-register binary operations, including BitVec bitwise compatibility.
- [x] Correct and prove context mapping for both operands of Loop `locValue`
  assignments in the Loop-to-Word/RISC-V bridge.
- [x] Add context-mapped Loop-to-Word/RISC-V agreements for byte loads and
  stores in the emitted shared-memory form, including zero-extension and byte
  truncation at the memory boundary.
- [x] Add context-mapped agreements for shared-memory halfword loads and
  stores, including the first little-endian byte observation.
- [x] Lift the one-step mapped expression agreements to a reusable
  context-indexed assignment simulation lemma.
- [x] Add reusable mapped LSL/LSR assignment simulation with an explicit
  source shift-count bound matching the RISC-V masking convention.
- [x] Prove preservation of the mapped-local relation across a destination
  update and corresponding non-aliasing RISC-V register write.
- [x] Prove mapped-local preservation for same-destination Loop `longMul`,
  including the emitted `mulHU`/`mul` sequence and source-register non-aliasing.
- [x] Prove mapped source-variable evaluation agrees with the compiled Word
  variable evaluation whenever the source local is present.
- [x] Prove the one-parameter call-boundary case: fresh Loop local binding
  agrees with cleared-and-bound Word registers under the mapped-local relation.
- [x] Prove that every source slot in the pipeline's `name ↦ name + 2`
  context is found with its mapped register name.
- [x] Compose the single-parameter Loop and Word binding lemmas into an
  explicit call-boundary state-agreement theorem.
- [x] Prove the handler-free single-parameter call simulation boundary,
  including argument transfer, callee-frame setup, return propagation, and
  preservation of the caller's mapped locals.
- [x] Add the handler-aware single-parameter call simulation boundary,
  including compatible callee normal/raise results, exception-register
  binding, handler resumption, and mapped-local preservation.
- [x] Add a concrete exception-handler call regression covering constant
  exception production, callee raise propagation, and handler continuation.
- [x] Prove control-result sequence composition for normal completion,
  returns, and raises under the combined Loop and handler-aware Word
  evaluators.
- [x] Prove mapped-local preservation across compiled register-register
  ADD/SUB/AND/OR/XOR assignments, including unchanged non-destination locals.
- [x] Prove mapped-local preservation across compiled LSL/LSR assignments,
  with the explicit bounded shift-count agreement.
- [x] Prove mapped-local preservation across compiled constant assignments,
  carrying the architectural x0 invariant.
- [x] Prove mapped-local preservation across compiled unsigned division,
  including the nonzero-divisor condition and DIVU result agreement.
- [x] Prove mapped-local preservation across compiled `locValue` moves,
  including preservation of all non-destination locals.
- [x] Prove successful two-step Loop/Word sequence evaluation decomposes
  through matching intermediate Loop and machine states.
- [x] Add the compositional sequence simulation rule that chains mapped-local
  preservation across both successful components.
- [x] Generalize the normal-path Loop-to-Word sequence simulation rule to
  arbitrary Loop fuel budgets.
- [x] Prove mapped Loop/Word condition agreement for equality, unsigned
  ordering, and HOL zero-test comparisons with immediate/register operands.
- [x] Prove Loop slot-analysis insertion helpers preserve duplicate-freeness,
  supporting later derivation of register non-aliasing invariants.
- [x] Prove RISC-V `registerOfNat` injectivity and derive pipeline-specific
  non-aliasing for distinct mapped source slots.
- [x] Extend Loop condition and expression evaluation to all comparison
  constructors, including HOL's zero-test convention for test/not-test.
- [x] Add an end-to-end declaration-call regression from Pancake through
  source semantics, Loop, Word, call-aware linking, Word semantics, and RV64
  execution, with a combined source/Word/machine agreement theorem.
- [x] Add an end-to-end conditional compiler-correctness theorem from source
  `if` through the linked RV64 artifact and architectural execution.
- [x] Exercise the same theorem shape with parameter-dependent equality
  branches on both equal and unequal RV64 inputs.
- [x] Add handler-aware source control-result semantics for the supported
  expression/call fragment, including exception matching, handler-variable
  binding, and a concrete raised-call regression.
- [x] Add an explicit source-level FFI handler boundary with evaluated
  arguments, caller-local state threading, and a concrete host-update
  regression.
- [x] Compose the source FFI boundary with nested calls and declaration-call
  result assignment in a fuel-bounded source regression.
- [x] Compose the source FFI boundary with the source call evaluator, allowing
  host effects inside a callee before declaration-call result propagation.
- [x] Integrate fuel-bounded source memory semantics for `while` loops, with
  verified immediate termination for false conditions.
- [x] Extend direct source memory semantics with structural `if` execution.
- [x] Add source equality-condition evaluation for local variables and a
  conditional-program regression.
- [x] Extend memory-backed source equality conditions through fuel-bounded
  conditional execution and add a load-based regression.
- [x] Extend scalar source expression semantics to subtraction, bitwise
  operations, all comparison constructors, and logical shifts, with executable
  Nat regressions.
- [x] Close the constant binary-expression RISC-V selector gap and prove
  end-to-end RV64 subtraction and bitwise pipeline regressions.
- [x] Add the first structured source-value evaluator, preserving words,
  raw/named records, field projection, globals, shaped loads, and stateful
  local/global/memory updates with executable regressions.
- [x] Extend the structured evaluator with fuel-bounded declaration calls,
  caller-local result binding, matching exception handlers, and an explicit
  structured FFI boundary with executable regressions.
- [x] Add structured control-result support for scoped declarations, stores,
  conditionals, while loops, break/continue, and shared-memory operations,
  with executable store/load and loop regressions.
- [x] Enforce structure-context well-formedness for structured loads, matching
  the source evaluator's shape-validation rule.
- [x] Connect the structured source evaluator to end-to-end declaration-call
  and FFI-call correctness fixtures.
- [x] Add an explicit source primitive-handler interface with a RISC-V
  `AddCarry` implementation and executable structured-evaluator regression.
- [x] Port CakeML's flat structured-memory load/store model, including
  consecutive word offsets, `Comb`/`Named` reconstruction, flattening, and
  failed-domain behavior.
- [x] Extend the flat source evaluator with fuel-bounded calls, scoped
  declaration calls, caught exceptions, loops, primitive dispatch, and FFI.
- [x] Add a handler-parameterized Loop evaluator for primitive dispatch and
  connect its RISC-V AddCarry handler to an executable Loop-to-Word agreement.
- [x] Prove a structured AddCarry source program through the composed
  Pancake/Crepe/Loop/Word straight-line RISC-V artifact.
- [x] Split the regression suite into focused modules under `Flapjack/Test`.
- [x] Split the RISC-V regression suite further into backend and flat-memory
  modules as the source-memory adapter grew.
- [x] Prove a pass-composed Crepe/flat-source structured store/load
  correctness bridge for flattened record payloads.
- [x] Prove a one-step Loop-to-Word FFI simulation theorem under an explicit
  RISC-V host-handler agreement, with a concrete register-mapped regression.
- [x] Prove the generated RISC-V FFI ABI move/`ECALL` sequence agrees with the
  abstract Word FFI handler under explicit non-clobber and service-width
  contracts.
- [x] Prove the ordinary single-parameter Loop-to-Word call boundary, including
  singleton result assignment and rejection of incompatible result arities.
- [x] Port the initial StackLang store-removal slice for fixed stores,
  `CurrHeap`, stack-frame allocation/free, and fixed/dynamic stack accesses,
  recursively rewriting nested control-flow and call bodies into explicit
  word-memory operations.
- [x] Lower the compact remaining StackLang store-removal equations for
  `OpCurrHeap`, stack-size conversion, and bitmap loads.
- [x] Expose the first executable StackLang → StackRemove → LabLang → RISC-V
  composition and test exact RV64 instruction output.
- [x] Lower StackLang `DataBufferWrite` to explicit word memory and verify the
  result through the RV64 backend.
- [x] Port the structured StackLang `StoreConsts` bitmap-copy lowering and
  verify that its generated loop compiles through the RV64 backend.
- [x] Add a concrete WordProg → Word-to-Stack → StackRemove → LabLang → RV64
  composition with an exact constant-lowering regression.
- [x] Add the width-indexed Word-to-Stack adapter and an actual
  `WordProg (Word width)` to RISC-V entry point, preserving bit-vector
  constants through the explicit Nat StackLang boundary.
- [x] Add explicit generated function entry labels and a cross-section
  StackLang program linker through LabLang and the RISC-V backend.
- [x] Wire the register-coloured Word function list through the actual
  Word-to-Stack, StackRemove, LabLang, and multi-section RISC-V pipeline, with
  an RV64 addition compilation regression.
- [x] Replace the fixed StackRemove fuel in all composed backend entry points
  with a size-derived bound, so generated functions are not limited to 1024
  levels of nesting.
- [x] Prove the non-`CurrHeap` StackRemove `Get` equation against the
  executable StackLang machine state under an explicit store-memory invariant.
- [x] Prove the matching non-`CurrHeap` StackRemove `Set` equation under
  explicit address/source non-aliasing conditions.
- [x] Prove the `CurrHeap` StackRemove fast-path simulations for both `Get`
  and `Set`.
- [x] Prove the bounded StackRemove stack-allocation equation under an
  explicit scratch/stack-pointer non-aliasing condition.
- [x] Prove StackRemove fixed-offset stack load/store simulations under
  explicit address-scratch and memory-write invariants.
- [ ] Port remaining handler/FFI lowering and a semantic simulation theorem
  for the complete pass.

## First implementation slice

The initial Lean commit implements stage 1's core in
`Flapjack/Language.lean`: shapes, polymorphic expressions, programs, function
and declaration syntax, `nestedSeq`, and shape sizing. The next slice should
port the nested-recursion measure and variable-use helpers, then the
static-checker data types and shape-context operations from
`panStaticScript.sml`, followed by a small executable checker. The static
data/context layer, expression variable-use helpers, Crepe IR, expression
lowering, and core structured statement lowering are now implemented; full
checking and semantic simulation remain the next increments.

## Verification workflow

- Lean: `lake build` from the repository root.
- HOL reference: `Holmake` in `cakeml/pancake` (and its relevant child
  directories).
- Keep commits small enough that a syntax/pass port and its proof obligations
  can be reviewed independently.
