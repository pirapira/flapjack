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
  amounts and backend selection tests; leave `ROR` explicit as unsupported by
  the base RV32I/RV64I target slice.
- [x] Extend Pancake/Crepe executable expression semantics with `PanOp.mul` and
  prove constant multiplication preservation through `pan_to_crep`.
- [x] Add a fuel-bounded Loop state/control-result evaluator for assignments,
  memory, returns, break/continue, conditionals, and loop execution.
- [x] Prove the first Crepe-to-Loop semantic bridge for constant return
  lowering through the generated temporary assignment.
- [x] Extend that bridge through Crepe `mul`/Loop `longMul` expansion and
  preserve the returned product.
- [ ] Port complete program checking, context transitions, and diagnostics.
- [ ] Add a structurally recursive loop evaluator and loop preservation theorem.
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
