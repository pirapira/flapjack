import Flapjack.PanToCrepSemantics
import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.PanValueFfiClockShiftFull

/-!
# From the clocked `pc_compile_correct` result relation to observational semantics

This module is the semantic counterpart of CakeML's
`state_rel_imp_semantics_to_crep` (`pan_to_crepProofScript.sml:4694`): it turns
the per-clock compiler result relation `panValuePcResultRel` into an
observational-semantics agreement `PanCrepSemanticAgreement`, and then into a
`panCrepBehaviourRel` between the two top-level semantics.

The source semantics observes `Return` and `FinalFFI` witnesses, treats any
other observation as a forbidden run, and otherwise assembles the FFI-event
prefix LUB.  The result relation `panValuePcResultRel` pins the constructor of
the target observation to the source constructor, so the same-clock failure and
success observations transport.  The genuinely cross-clock obligations are the
*choice-stability* obligations of CakeML's original proof; for the no-final-FFI
fragment used below they reduce to "every successful observation is a
`Return`", which is exactly the shape a later `finalFfi`-carrying instantiation
has to strengthen with the monotone-evaluator theorem.
-/

namespace Flapjack

/-! ## The concrete source evaluator hook

`PanSemanticsHooks` is intentionally evaluator-agnostic so the semantic
transport lemmas can be reused by small tests.  The production Pancake
semantics, however, evaluates a fixed source program at each clock.  This
adapter exposes the actual `panSemEvaluate` entry point at that boundary; in
particular, it does not replace the clocked evaluator by the older compact
compatibility evaluator.  Keeping this definition here avoids a dependency
cycle between `PanEvaluate` and `PanObservationalSemantics`.
-/

def panSemEvaluateHooks
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α) : PanSemanticsHooks α σ where
  evaluate clock :=
    panSemEvaluate context primitive handler { state with clock := clock } program
  ffiOutcome event := event.outcome

@[simp] theorem panSemEvaluateHooks_evaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α) (clock : Nat) :
    (panSemEvaluateHooks context primitive handler state program).evaluate clock =
      panSemEvaluate context primitive handler { state with clock := clock } program := by
  rfl

/-! Cake's clock-monotonicity proof produces a prefix for each ordered pair of
    evaluator states, while the observational wrapper consumes the weaker
    unordered-chain predicate.  This bridge makes that stateful evaluator
    obligation explicit and discharges the chain by totality of `Nat.le`. -/
theorem panLprefixChain_of_panSemEvaluate_event_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (hprefix : ∀ (left right : Nat), left ≤ right →
      panResultEvents
          (panSemEvaluate context primitive handler
            { state with clock := left } program) <+:
        panResultEvents
          (panSemEvaluate context primitive handler
            { state with clock := right } program)) :
    panLprefixChain (fun clock =>
      panResultEvents
        (panSemEvaluate context primitive handler
          { state with clock := clock } program)) := by
  intro left right
  rcases Nat.le_total left right with hleft | hright
  · exact Or.inl (hprefix left right hleft)
  · exact Or.inr (hprefix right left hright)

/-! The non-timeout source evaluator supplies the ordered prefixes needed by
    `panSemantics` directly.  Timeout monotonicity remains an explicit
    supported-subset obligation until the recursive Cake evaluator induction
    is discharged. -/
theorem panLprefixChain_of_panSemEvaluate_nonTimeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (hevaluate : ∀ clock, ∃ outcome returnedClock,
      panSemEvaluate context primitive handler
        { state with clock := clock } program = some (outcome, returnedClock))
    (hnonTimeout : ∀ clock outcome returnedClock,
      panSemEvaluate context primitive handler
        { state with clock := clock } program = some (outcome, returnedClock) →
      ∀ locals globals memory ffi,
        outcome ≠ .timeout locals globals memory ffi) :
    panLprefixChain (fun clock =>
      panResultEvents
        (panSemEvaluate context primitive handler
          { state with clock := clock } program)) := by
  apply panLprefixChain_of_panSemEvaluate_event_prefix
    context primitive handler state program
  intro left right hleft
  exact panSemEvaluate_clock_event_prefix_of_nonTimeout
    context primitive handler state program hevaluate hnonTimeout left right hleft

/-! Expose the same non-timeout chain at the production hook boundary used by
    the clock-indexed semantic agreement.  The evaluator and non-timeout
    premises stay in the executable `panSemEvaluate` form; only the hook
    projection is discharged definitionally. -/
theorem panSemEvaluateHooks_lprefixChain_of_nonTimeout
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (hevaluate : ∀ clock, ∃ outcome returnedClock,
      panSemEvaluate context primitive handler
        { state with clock := clock } program = some (outcome, returnedClock))
    (hnonTimeout : ∀ clock outcome returnedClock,
      panSemEvaluate context primitive handler
        { state with clock := clock } program = some (outcome, returnedClock) →
      ∀ locals globals memory ffi,
        outcome ≠ .timeout locals globals memory ffi) :
    panLprefixChain (fun clock =>
      panResultEvents
        ((panSemEvaluateHooks context primitive handler state program).evaluate clock)) := by
  have hchain := panLprefixChain_of_panSemEvaluate_nonTimeout
    context primitive handler state program hevaluate hnonTimeout
  simpa [panSemEvaluateHooks] using hchain

@[simp] theorem panSemEvaluateHooks_ffiOutcome
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α) (event : FfiFinalEvent) :
    (panSemEvaluateHooks context primitive handler state program).ffiOutcome event =
      event.outcome := by
  rfl

/-! Once the concrete source evaluator has been shown to satisfy the
    `PanCrepSemanticAgreement` record, this is the direct top-level behavior
    statement.  The agreement remains an explicit premise: it is the ported
    analogue of the per-clock `pc_compile_correct` and choice-stability work in
    Cake's `state_rel_imp_semantics_to_crep` proof, and must not be replaced by
    an unproved compatibility axiom. -/
theorem panCrepBehaviourRel_of_panSemEvaluate_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (program : Prog α)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement
      (panSemEvaluateHooks context primitive handler state program) crepHooks)
    (panChain : panLprefixChain
      (fun clock => panResultEvents
        ((panSemEvaluateHooks context primitive handler state program).evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics (panSemEvaluateHooks context primitive handler state program)
        panChain)
      (crepSemantics crepHooks crepChain) := by
  exact panSemantics_rel_crepSemantics
    (panSemEvaluateHooks context primitive handler state program) crepHooks
    agreement panChain crepChain

/-! ## Clocked results as compact `pc` results -/

/-- Project a clocked source outcome onto the compact `pc_compile_correct`
source result.  The `finalFfi` control case keeps the event, and `timeout`
becomes the compact `timeout` result. -/
def panOutcomeToPcResult : PanValueFfiClockOutcome α σ → PanValuePcResult α
  | .control (.normal locals globals memory _) => .normal locals globals memory
  | .control (.returned locals globals memory _ values) =>
      .returned locals globals memory values
  | .control (.raised locals globals memory _ exception value) =>
      .raised locals globals memory exception value
  | .control (.broke locals globals memory _) => .broke locals globals memory
  | .control (.continued locals globals memory _) => .continued locals globals memory
  | .control (.finalFfi locals globals memory _ event) =>
      .finalFfi locals globals memory event
  | .timeout locals globals memory _ => .timeout locals globals memory

/-- Project a Crep control result onto the compact `pc_compile_correct` target
result.  Unlike the boundary bridge, `finalFfi` is retained: the observational
semantics treats it as a successful observation. -/
def crepControlToPcResult : CrepControlResult α → CrepPcResult α
  | .normal state => .normal state
  | .returned state values => .returned state values
  | .raised state exception => .raised state exception
  | .broke state label => .broke state label
  | .continued state label => .continued state label
  | .finalFfi state event => .finalFfi state event

/-! ## Clocked evaluator adapters

The compact `pc_compile_correct` boundary quantifies over an evaluator whose
clock is implicit in the evaluator value.  The production semantics exposes
that clock explicitly through `panSemEvaluate` and `crepEvaluate`.  These
adapters make the correspondence executable: fixing a clock produces a
`PanValuePcEvaluator`/`CrepPcEvaluator`, while retaining timeout and
`FinalFFI` in the result constructors.  The adapter lemmas below are the
small, reusable link needed when the stateful program proofs are assembled
into the clocked Cake theorem; they do not assert any compiler correctness by
themselves.
-/

def panValuePcClockedSourceEvaluator
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (clock : Nat)
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ) : PanValuePcEvaluator α :=
  fun _ input program =>
    (panSemEvaluate context primitive handler
      { state with
        structs := input.structs
        locals := input.locals
        globals := input.globals
        memory := input.memory
        clock := clock } program).map
      (fun result =>
        { code := input.code
          eshapes := input.eshapes
          result := panOutcomeToPcResult result.1 })

def crepPcClockedTargetEvaluator
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (clock : Nat)
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) : CrepPcEvaluator α :=
  fun _ input program =>
    (crepEvaluate functions primitive ffi sharedMem baseAddress topAddress
      clock input.state program).map
      (fun result =>
        { code := input.code
          eshapes := input.eshapes
          result := crepControlToPcResult result })

theorem panValuePcClockedSourceEvaluator_adapter
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (clock : Nat) (compileContext : CompileContext α)
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ)
    (input : PanValuePcInput α) (program : Prog α)
    (execution : PanValuePcExecution α)
    (heval : panValuePcClockedSourceEvaluator clock context primitive handler
      state compileContext input program = some execution) :
    ∃ result,
      panSemEvaluate context primitive handler
        { state with
          structs := input.structs
          locals := input.locals
          globals := input.globals
          memory := input.memory
          clock := clock } program = some result ∧
      execution.result = panOutcomeToPcResult result.1 := by
  cases hsource : panSemEvaluate context primitive handler
      { state with
        structs := input.structs
        locals := input.locals
        globals := input.globals
        memory := input.memory
        clock := clock } program with
  | none => simp [panValuePcClockedSourceEvaluator, hsource] at heval
  | some result =>
      refine ⟨result, ?_, ?_⟩
      · rfl
      have heval' :
          ({ code := input.code
            , eshapes := input.eshapes
            , result := panOutcomeToPcResult result.1 } :
            PanValuePcExecution α) = execution := by
        simpa [panValuePcClockedSourceEvaluator, hsource] using heval
      exact (congrArg (fun value : PanValuePcExecution α => value.result)
        heval').symm

theorem crepPcClockedTargetEvaluator_adapter
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (clock : Nat) (compileContext : CompileContext α)
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (input : CrepPcInput α)
    (program : CrepProg α) (execution : CrepPcExecution α)
    (heval : crepPcClockedTargetEvaluator clock functions primitive ffi sharedMem
      baseAddress topAddress compileContext input program = some execution) :
    ∃ result,
      crepEvaluate functions primitive ffi sharedMem baseAddress topAddress
        clock input.state program = some result ∧
      execution.result = crepControlToPcResult result := by
  cases htarget : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress clock input.state program with
  | none => simp [crepPcClockedTargetEvaluator, crepEvaluate, htarget] at heval
  | some result =>
      refine ⟨result, ?_, ?_⟩
      · simpa [crepEvaluate] using htarget
      have heval' :
          ({ code := input.code
            , eshapes := input.eshapes
            , result := crepControlToPcResult result } :
            CrepPcExecution α) = execution := by
        simpa [crepPcClockedTargetEvaluator, crepEvaluate, htarget] using heval
      exact (congrArg (fun value : CrepPcExecution α => value.result)
        heval').symm

/-! Cake's `state_rel_imp_semantics_to_crep` dispatches the ordinary,
    raised, and clock-exhaustion call results through one declaration
    boundary.  Keep that composition explicit here: the source call result
    is selected by the three-way case witness, the declaration evaluator is
    still executed by the public program evaluator, and the concrete
    `panValuePcResultRel` is carried through to the corresponding target
    result.  This is deliberately limited to the non-returning call cases;
    returned calls additionally need the callee return-shape premise.

    This theorem lives with the `pc` result relation rather than the low-level
    clock evaluator so the import graph remains acyclic. -/
theorem evalPanValueFfiClockProgram_of_declarations_and_normal_raised_timeout_call_result_rel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (state : PanValueProgramState α)
    (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (hdeclarations : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) = some state)
    (hentry : lookupInfo entry state.returnShapes = none)
    (hcase :
      (∃ (locals globals : VarName → Option (PanValue α))
          (memory : α → Option (PanValue α)) (ffi : FfiState σ)
          (nextClock : Nat),
        evalPanValueFfiClockCall context primitive handler state.structs
          state.functions state.baseAddress state.topAddress state.bytesInWord fuel
          (fun _ => none) state.globals state.memory initial.ffi clock none entry
          arguments (memoryAccess := memoryAccess)
          (contracts := some (PanValueCallContracts.mk state.returnShapes
            state.exceptions state.parameterShapes))
          (memoryHandler := memoryHandler) =
          some (.control (.normal locals globals memory ffi), nextClock) ∧
        ∃ targetResult : CrepPcResult α,
          panValuePcResultRel state.structs pcContext exceptionRel
            exceptionCode globalsLookup
            (.normal locals globals memory) targetResult)
      ∨ (∃ (globals : VarName → Option (PanValue α))
          (memory : α → Option (PanValue α)) (ffi : FfiState σ)
          (exception : ExceptionId) (value : PanValue α)
          (nextClock : Nat),
        evalPanValueFfiClockCall context primitive handler state.structs
          state.functions state.baseAddress state.topAddress state.bytesInWord fuel
          (fun _ => none) state.globals state.memory initial.ffi clock none entry
          arguments (memoryAccess := memoryAccess)
          (contracts := some (PanValueCallContracts.mk state.returnShapes
            state.exceptions state.parameterShapes))
          (memoryHandler := memoryHandler) =
          some (.control (.raised (fun _ => none) globals memory ffi
            exception value), nextClock) ∧
        ∃ targetResult : CrepPcResult α,
          panValuePcResultRel state.structs pcContext exceptionRel
            exceptionCode globalsLookup
            (.raised (fun _ => none) globals memory exception value) targetResult)
      ∨ (∃ (globals : VarName → Option (PanValue α))
          (memory : α → Option (PanValue α)) (ffi : FfiState σ)
          (nextClock : Nat),
        evalPanValueFfiClockCall context primitive handler state.structs
          state.functions state.baseAddress state.topAddress state.bytesInWord fuel
          (fun _ => none) state.globals state.memory initial.ffi clock none entry
          arguments (memoryAccess := memoryAccess)
          (contracts := some (PanValueCallContracts.mk state.returnShapes
            state.exceptions state.parameterShapes))
          (memoryHandler := memoryHandler) =
          some (.timeout (fun _ => none) globals memory ffi, nextClock) ∧
        ∃ targetResult : CrepPcResult α,
          panValuePcResultRel state.structs pcContext exceptionRel
            exceptionCode globalsLookup
            (.timeout (fun _ => none) globals memory) targetResult)) :
    ∃ (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
        (targetResult : CrepPcResult α),
      evalPanValueFfiClockProgram context initial clock primitive handler fuel
        declarations entry arguments (memoryAccess := memoryAccess)
        (memoryHandler := memoryHandler) = some (outcome, nextClock) ∧
      panValuePcResultRel state.structs pcContext exceptionRel exceptionCode
        globalsLookup (panOutcomeToPcResult outcome) targetResult := by
  rcases hcase with hnormal | hraised | htimeout
  · obtain ⟨locals, globals, memory, ffi, nextClock, hcall,
      targetResult, hresult⟩ := hnormal
    refine ⟨.control (.normal locals globals memory ffi), nextClock,
      targetResult, ?_, ?_⟩
    · exact evalPanValueFfiClockProgram_of_declarations_and_call
        context initial clock primitive handler fuel declarations entry arguments state
        (.control (.normal locals globals memory ffi)) nextClock memoryAccess
        memoryHandler hdeclarations hentry hcall
    · simpa [panOutcomeToPcResult] using hresult
  · obtain ⟨globals, memory, ffi, exception, value, nextClock, hcall,
      targetResult, hresult⟩ := hraised
    refine ⟨.control (.raised (fun _ => none) globals memory ffi exception value),
      nextClock, targetResult, ?_, ?_⟩
    · exact evalPanValueFfiClockProgram_of_declarations_and_call
        context initial clock primitive handler fuel declarations entry arguments state
        (.control (.raised (fun _ => none) globals memory ffi exception value))
        nextClock memoryAccess memoryHandler hdeclarations hentry hcall
    · simpa [panOutcomeToPcResult] using hresult
  · obtain ⟨globals, memory, ffi, nextClock, hcall, targetResult, hresult⟩ := htimeout
    refine ⟨.timeout (fun _ => none) globals memory ffi, nextClock,
      targetResult, ?_, ?_⟩
    · exact evalPanValueFfiClockProgram_of_declarations_and_call
        context initial clock primitive handler fuel declarations entry arguments state
        (.timeout (fun _ => none) globals memory ffi) nextClock memoryAccess
        memoryHandler hdeclarations hentry hcall
    · simpa [panOutcomeToPcResult] using hresult

/-! Consume both executable clock adapters at the result-relation boundary.
    This is the concrete link from the production stateful evaluators to the
    arbitrary `pc_compile_correct` result relation: the source and target
    evaluator equations, their states, and the context-coded result relation
    remain explicit, including returned, raised, timeout, and final-FFI cases. -/
theorem panValuePcResultRelWithContextCode_of_clocked_evaluator_adapters
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (clock : Nat) (sourceCompileContext targetCompileContext : CompileContext α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (sourceState : PanSemEvaluateState α σ)
    (sourceInput : PanValuePcInput α) (sourceProgram : Prog α)
    (sourceExecution : PanValuePcExecution α)
    (targetFunctions : List (CompiledFunction α))
    (targetPrimitive : CrepPrimitiveHandler α)
    (targetFfi : CrepFfiHandler α)
    (targetSharedMem : CrepSharedMemHandler α)
    (targetBaseAddress targetTopAddress : α)
    (targetInput : CrepPcInput α) (targetProgram : CrepProg α)
    (targetExecution : CrepPcExecution α)
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hsource : panValuePcClockedSourceEvaluator clock sourceContext
      sourcePrimitive sourceHandler sourceState sourceCompileContext sourceInput
      sourceProgram = some sourceExecution)
    (htarget : crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive
      targetFfi targetSharedMem targetBaseAddress targetTopAddress
      targetCompileContext targetInput targetProgram = some targetExecution)
    (hresult : panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceExecution.result targetExecution.result) :
    ∃ sourceResult targetResult,
      panSemEvaluate sourceContext sourcePrimitive sourceHandler
        { sourceState with
          structs := sourceInput.structs
          locals := sourceInput.locals
          globals := sourceInput.globals
          memory := sourceInput.memory
          clock := clock } sourceProgram = some sourceResult ∧
      crepEvaluate targetFunctions targetPrimitive targetFfi targetSharedMem
        targetBaseAddress targetTopAddress clock targetInput.state targetProgram =
        some targetResult ∧
      panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
        globalsLookup (panOutcomeToPcResult sourceResult.1)
        (crepControlToPcResult targetResult) ∧
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult sourceResult.1) (crepControlToPcResult targetResult) := by
  rcases panValuePcClockedSourceEvaluator_adapter clock sourceCompileContext
    sourceContext sourcePrimitive sourceHandler sourceState sourceInput sourceProgram
    sourceExecution hsource with ⟨sourceResult, hsourceEval, hsourceResult⟩
  rcases crepPcClockedTargetEvaluator_adapter clock targetCompileContext
    targetFunctions targetPrimitive targetFfi targetSharedMem targetBaseAddress
    targetTopAddress targetInput targetProgram targetExecution htarget with
    ⟨targetResult, htargetEval, htargetResult⟩
  refine ⟨sourceResult, targetResult, hsourceEval, htargetEval, ?_, ?_⟩
  · simpa [hsourceResult, htargetResult] using hresult
  · exact panValuePcResultRel_of_withContextCode structs context exceptionRel
      exceptionCode globalsLookup (panOutcomeToPcResult sourceResult.1)
      (crepControlToPcResult targetResult) (by
        simpa [hsourceResult, htargetResult] using hresult)

/-! Complete the adapter link at the plain top-level correctness boundary.
    The compiler relation is obtained only by projecting an explicit
    context-coded correctness premise; the executable source/Crep equations
    and their arbitrary result constructor remain visible in the conclusion. -/
theorem panValuePcCompileCorrectAndClockedResultRel_of_clocked_evaluator_adapters
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (sourceState : PanSemEvaluateState α σ)
    (clock : Nat) (sourceCompileContext targetCompileContext : CompileContext α)
    (targetFunctions : List (CompiledFunction α))
    (targetPrimitive : CrepPrimitiveHandler α)
    (targetFfi : CrepFfiHandler α)
    (targetSharedMem : CrepSharedMemHandler α)
    (targetBaseAddress targetTopAddress : α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (sourceInput : PanValuePcInput α) (sourceProgram : Prog α)
    (sourceExecution : PanValuePcExecution α)
    (targetInput : CrepPcInput α) (targetProgram : CrepProg α)
    (targetExecution : CrepPcExecution α)
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompile : PanValuePcCompileCorrectWithContextCode
      (panValuePcClockedSourceEvaluator clock sourceContext sourcePrimitive
        sourceHandler sourceState)
      (crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive targetFfi
        targetSharedMem targetBaseAddress targetTopAddress)
      codeRel excpRel exceptionCode globalsLookup program)
    (hsource : panValuePcClockedSourceEvaluator clock sourceContext
      sourcePrimitive sourceHandler sourceState sourceCompileContext sourceInput
      sourceProgram = some sourceExecution)
    (htarget : crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive
      targetFfi targetSharedMem targetBaseAddress targetTopAddress
      targetCompileContext targetInput targetProgram = some targetExecution)
    (hresult : panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrect
      (panValuePcClockedSourceEvaluator clock sourceContext sourcePrimitive
        sourceHandler sourceState)
      (crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive targetFfi
        targetSharedMem targetBaseAddress targetTopAddress)
      codeRel excpRel exceptionCode globalsLookup program ∧
    ∃ sourceResult targetResult,
      panSemEvaluate sourceContext sourcePrimitive sourceHandler
        { sourceState with
          structs := sourceInput.structs
          locals := sourceInput.locals
          globals := sourceInput.globals
          memory := sourceInput.memory
          clock := clock } sourceProgram = some sourceResult ∧
      crepEvaluate targetFunctions targetPrimitive targetFfi targetSharedMem
        targetBaseAddress targetTopAddress clock targetInput.state targetProgram =
        some targetResult ∧
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult sourceResult.1) (crepControlToPcResult targetResult) := by
  have hplain := panValuePcCompileCorrect_of_withContextCode
    (panValuePcClockedSourceEvaluator clock sourceContext sourcePrimitive sourceHandler
      sourceState)
    (crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive targetFfi
      targetSharedMem targetBaseAddress targetTopAddress)
    codeRel excpRel exceptionCode globalsLookup program hcompile
  have hresults := panValuePcResultRelWithContextCode_of_clocked_evaluator_adapters
    clock sourceCompileContext targetCompileContext sourceContext sourcePrimitive
    sourceHandler sourceState sourceInput sourceProgram sourceExecution targetFunctions
    targetPrimitive targetFfi targetSharedMem targetBaseAddress targetTopAddress targetInput
    targetProgram targetExecution structs context exceptionRel exceptionCode globalsLookup
    hsource htarget hresult
  rcases hresults with ⟨sourceResult, targetResult, hsourceEval, htargetEval,
    _hcontextResult, hplainResult⟩
  exact ⟨hplain, ⟨sourceResult, targetResult, hsourceEval, htargetEval, hplainResult⟩⟩
/-! ## Same-clock field transport -/

set_option linter.unusedSimpArgs false in
/-- Forbidden-ness transports across `panValuePcResultRel`: the relation never
maps a forbidden observation to a successful one or conversely. -/
theorem panValuePcResultRel_forbidden_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult)) :
    panForbiddenResult (some (outcome, returnedClock)) ↔
      crepForbiddenResult (crepControlResultToSemantic (some crepResult)) := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panForbiddenResult, crepForbiddenResult,
          panValuePcResultRel]
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panForbiddenResult, crepForbiddenResult,
          panValuePcResultRel]

set_option linter.unusedSimpArgs false in
/-- Successful-ness transports across `panValuePcResultRel`. -/
theorem panValuePcResultRel_success_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult)) :
    (∃ sourceOutcome,
        panResultOutcome panHooks (some (outcome, returnedClock)) =
          some sourceOutcome) ↔
      (∃ targetOutcome,
        crepResultOutcome (crepControlResultToSemantic (some crepResult)) =
          some targetOutcome) := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panValuePcResultRel]
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panValuePcResultRel]

set_option linter.unusedSimpArgs false in
/-- Same-clock successful observations relate: a `Return`/`Return` pair is
`success`/`success`, and a `FinalFFI`/`FinalFFI` pair shares the event (hence
the outcome, when the source hook reads `event.outcome`). -/
theorem panValuePcResultRel_success_outcome
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat) (sourceOutcome : PanSemanticOutcome)
    (targetOutcome : CrepSemanticOutcome)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult))
    (hsource : panResultOutcome panHooks (some (outcome, returnedClock)) =
      some sourceOutcome)
    (htarget : crepResultOutcome (crepControlResultToSemantic (some crepResult)) =
      some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panCrepSemanticOutcomeRel, panValuePcResultRel, hffiOutcome] <;>
        (try (subst sourceOutcome; subst targetOutcome;
              simp [panCrepSemanticOutcomeRel, hffiOutcome]))
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panCrepSemanticOutcomeRel, panValuePcResultRel] <;>
        (try (subst sourceOutcome; subst targetOutcome;
              simp [panCrepSemanticOutcomeRel, hffiOutcome]))

/-- The Pancake observational outcome of a clocked result is the outcome the
    compiler-correctness projection assigns to its `PanValuePcResult`: normal,
    raised, broke, continued and timeout observations are non-successful on both
    sides, while `Return` and `FinalFFI` agree (the latter needs the source hook
    to read `event.outcome`). -/
theorem panResultOutcome_eq_pcResultOutcome
    (panHooks : PanSemanticsHooks α σ)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (outcome : PanValueFfiClockOutcome α σ) (returnedClock : Nat) :
    panResultOutcome panHooks (some (outcome, returnedClock)) =
      panValuePcResultOutcome (panOutcomeToPcResult outcome) := by
  cases outcome with
  | control result =>
      cases result <;>
        simp [panResultOutcome, panOutcomeToPcResult, panValuePcResultOutcome,
          hffiOutcome]
  | timeout locals globals memory ffi =>
      simp [panResultOutcome, panOutcomeToPcResult, panValuePcResultOutcome]

/-- The Crep observational outcome of a control result is the outcome the
    compiler-correctness projection assigns to its `CrepPcResult`; the `normal`
    result is non-successful on both sides. -/
theorem crepResultOutcome_eq_pcResultOutcome
    (result : CrepControlResult α) :
    crepResultOutcome (crepControlResultToSemantic (some result)) =
      crepPcResultOutcome (crepControlToPcResult result) := by
  cases result <;>
    simp [crepControlResultToSemantic, crepControlToPcResult, crepResultOutcome,
      crepPcResultOutcome]

/-- The constructor-level semantic lift: a `panValuePcResultRel` pair together
    with the two same-clock semantic outcome witnesses yields
    `panCrepSemanticOutcomeRel`.  This transports the HOL
    `state_rel_imp_semantics_to_crep` constructor step through the evaluator
    outcome projections, so it also covers a `FinalFFI` observation. -/
theorem panValuePcResultRel_semanticOutcomeRel_of_outcome
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat) (sourceOutcome : PanSemanticOutcome)
    (targetOutcome : CrepSemanticOutcome)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult))
    (hsource : panResultOutcome panHooks (some (outcome, returnedClock)) =
      some sourceOutcome)
    (htarget : crepResultOutcome (crepControlResultToSemantic (some crepResult)) =
      some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  rw [panResultOutcome_eq_pcResultOutcome panHooks hffiOutcome outcome
    returnedClock] at hsource
  rw [crepResultOutcome_eq_pcResultOutcome crepResult] at htarget
  exact panValuePcResultRel_semanticOutcomeRel structs context exceptionRel
    exceptionCode globalsLookup (panOutcomeToPcResult outcome)
    (crepControlToPcResult crepResult) sourceOutcome targetOutcome hrel hsource
    htarget

/-! A cross-clock result relation is the missing choice-stability premise for
the observational agreement. Unlike the no-final-FFI agreement constructor,
this helper preserves the `Return`/`FinalFFI` distinction and therefore also
covers a terminal FFI result. -/
theorem panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceClock targetClock : Nat)
    (sourceOutcome : PanValueFfiClockOutcome α σ)
    (returnedClock : Nat)
    (targetResult : CrepControlResult α)
    (targetState : CrepState α)
    (sourceSemanticOutcome : PanSemanticOutcome)
    (targetSemanticOutcome : CrepSemanticOutcome)
    (_hsource : panHooks.evaluate sourceClock =
      some (sourceOutcome, returnedClock))
    (_htarget : crepHooks.evaluate targetClock =
      (crepControlResultToSemantic (some targetResult), targetState))
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult sourceOutcome)
      (crepControlToPcResult targetResult))
    (hsourceOutcome : panResultOutcome panHooks
      (some (sourceOutcome, returnedClock)) = some sourceSemanticOutcome)
    (htargetOutcome : crepResultOutcome
      (crepControlResultToSemantic (some targetResult)) =
      some targetSemanticOutcome) :
    panCrepSemanticOutcomeRel sourceSemanticOutcome targetSemanticOutcome := by
  exact panValuePcResultRel_semanticOutcomeRel_of_outcome
    structs context exceptionRel exceptionCode globalsLookup panHooks
    hffiOutcome sourceOutcome targetResult returnedClock sourceSemanticOutcome
    targetSemanticOutcome hrel hsourceOutcome htargetOutcome

/-! ## The agreement from clocked compiler evidence -/

/-- Build a `PanCrepSemanticAgreement` from a per-clock `panValuePcResultRel`
relation between the source and target evaluators.

`hrel` is the `pc_compile_correct` result relation instantiated at each clock;
`hevents` is the FFI-trace component that the relation deliberately does not
carry.  The two `Success` hypotheses are the no-final-FFI choice-stability
obligations: in the no-final-FFI fragment every successful observation is a
`Return`, so the cross-clock outcome fields of the agreement are immediate.
A later `finalFfi`-carrying instantiation replaces them with the
monotone-evaluator theorem. -/
theorem panCrepSemanticAgreement_of_pcResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ) (crepHooks : CrepSemanticsHooks α)
    (_hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hpanEval : ∀ clock, ∃ outcome returnedClock,
      panHooks.evaluate clock = some (outcome, returnedClock))
    (hcrepEval : ∀ clock, ∃ result state,
      crepHooks.evaluate clock =
        (crepControlResultToSemantic (some result), state))
    (hrel : ∀ clock outcome returnedClock result,
      panHooks.evaluate clock = some (outcome, returnedClock) →
      (crepHooks.evaluate clock).1 = crepControlResultToSemantic (some result) →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult outcome) (crepControlToPcResult result))
    (hevents : ∀ clock,
      panResultEvents (panHooks.evaluate clock) =
        crepHooks.ioEvents (crepHooks.evaluate clock).2)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro clock
    exact hevents clock
  · intro clock
    obtain ⟨outcome, returnedClock, hpanClock⟩ := hpanEval clock
    obtain ⟨result, state, hcrepClock⟩ := hcrepEval clock
    rw [hpanClock, hcrepClock]
    exact panValuePcResultRel_forbidden_iff structs context exceptionRel
      exceptionCode globalsLookup outcome result returnedClock
      (hrel clock outcome returnedClock result hpanClock (by rw [hcrepClock]))
  · intro clock
    obtain ⟨outcome, returnedClock, hpanClock⟩ := hpanEval clock
    obtain ⟨result, state, hcrepClock⟩ := hcrepEval clock
    have hpanAt : panSuccessfulAt panHooks clock ↔
        ∃ sourceOutcome,
          panResultOutcome panHooks (some (outcome, returnedClock)) =
            some sourceOutcome := by
      constructor
      · rintro ⟨result', outcome', heval, houtcome⟩
        rw [hpanClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨sourceOutcome, houtcome⟩
        exact ⟨(outcome, returnedClock), sourceOutcome, hpanClock, houtcome⟩
    have hcrepAt : crepSuccessfulAt crepHooks clock ↔
        ∃ targetOutcome,
          crepResultOutcome
            (crepControlResultToSemantic (some result)) = some targetOutcome := by
      constructor
      · rintro ⟨result', state', outcome', heval, houtcome⟩
        rw [hcrepClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨targetOutcome, houtcome⟩
        exact ⟨crepControlResultToSemantic (some result), state, targetOutcome,
          hcrepClock, houtcome⟩
    rw [hpanAt, hcrepAt]
    exact panValuePcResultRel_success_iff structs context exceptionRel
      exceptionCode globalsLookup panHooks outcome result returnedClock
      (hrel clock outcome returnedClock result hpanClock (by rw [hcrepClock]))
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    have hsourceKind := hpanSuccess sourceClock sourceResult sourceOutcome
      hsource hsourceOutcome
    have htargetKind := hcrepSuccess targetClock targetResult targetState
      targetOutcome htarget htargetOutcome
    rw [hsourceKind, htargetKind]
    simp [panCrepSemanticOutcomeRel]
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    rw [hpanSuccessEvents sourceClock sourceResult sourceOutcome hsource
        hsourceOutcome,
      hcrepSuccessEvents targetClock targetResult targetState targetOutcome
        htarget htargetOutcome]


/-! ## The agreement from a per-clock result pair

The theorem above takes the pointwise relation through the *semantic* projection
`crepControlResultToSemantic`, which forgets the target state in the `normal`
case.  The version below instead asks for the raw target `CrepControlResult`
and state, together with the event equality, at each clock.  This is the shape a
concrete compiler instantiation can discharge. -/
theorem panCrepSemanticAgreement_of_pcResultRel_pair
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ) (crepHooks : CrepSemanticsHooks α)
    (hpair : ∀ clock, ∃ (outcome : PanValueFfiClockOutcome α σ)
      (returnedClock : Nat) (result : CrepControlResult α) (state : CrepState α),
      panHooks.evaluate clock = some (outcome, returnedClock) ∧
      crepHooks.evaluate clock =
        (crepControlResultToSemantic (some result), state) ∧
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult outcome) (crepControlToPcResult result) ∧
      panResultEvents (some (outcome, returnedClock)) = crepHooks.ioEvents state)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, _,
      hevents⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact hevents
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact panValuePcResultRel_forbidden_iff structs context exceptionRel
      exceptionCode globalsLookup outcome result returnedClock hrel
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    have hpanAt : panSuccessfulAt panHooks clock ↔
        ∃ sourceOutcome,
          panResultOutcome panHooks (some (outcome, returnedClock)) =
            some sourceOutcome := by
      constructor
      · rintro ⟨result', outcome', heval, houtcome⟩
        rw [hpanClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨sourceOutcome, houtcome⟩
        exact ⟨(outcome, returnedClock), sourceOutcome, hpanClock, houtcome⟩
    have hcrepAt : crepSuccessfulAt crepHooks clock ↔
        ∃ targetOutcome,
          crepResultOutcome
            (crepControlResultToSemantic (some result)) = some targetOutcome := by
      constructor
      · rintro ⟨result', state', outcome', heval, houtcome⟩
        rw [hcrepClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨targetOutcome, houtcome⟩
        exact ⟨crepControlResultToSemantic (some result), state, targetOutcome,
          hcrepClock, houtcome⟩
    rw [hpanAt, hcrepAt]
    exact panValuePcResultRel_success_iff structs context exceptionRel
      exceptionCode globalsLookup panHooks outcome result returnedClock hrel
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    have hsourceKind := hpanSuccess sourceClock sourceResult sourceOutcome
      hsource hsourceOutcome
    have htargetKind := hcrepSuccess targetClock targetResult targetState
      targetOutcome htarget htargetOutcome
    rw [hsourceKind, htargetKind]
    simp [panCrepSemanticOutcomeRel]
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    rw [hpanSuccessEvents sourceClock sourceResult sourceOutcome hsource
        hsourceOutcome,
      hcrepSuccessEvents targetClock targetResult targetState targetOutcome
      htarget htargetOutcome]

/-! Full agreement with the Cake-style cross-clock choice premise. The raw
target result and event equality stay explicit so the constructor can be
instantiated by the monotone evaluator proof without treating FinalFFI as a
Return or erasing its trace. -/
theorem panCrepSemanticAgreement_of_pcResultRel_pair_cross_clock
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ) (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hpair : ∀ clock, ∃ (outcome : PanValueFfiClockOutcome α σ)
      (returnedClock : Nat) (result : CrepControlResult α) (state : CrepState α),
      panHooks.evaluate clock = some (outcome, returnedClock) ∧
      crepHooks.evaluate clock =
        (crepControlResultToSemantic (some result), state) ∧
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult outcome) (crepControlToPcResult result) ∧
      panResultEvents (some (outcome, returnedClock)) = crepHooks.ioEvents state)
    (hcross : ∀ (sourceClock targetClock : Nat)
      (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome)
      (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      panHooks.evaluate sourceClock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      crepHooks.evaluate targetClock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      ∃ (outcome : PanValueFfiClockOutcome α σ) (returnedClock : Nat)
        (result : CrepControlResult α),
        sourceResult = (outcome, returnedClock) ∧
        targetResult = crepControlResultToSemantic (some result) ∧
        panValuePcResultRel structs context exceptionRel exceptionCode
          globalsLookup (panOutcomeToPcResult outcome) (crepControlToPcResult result) ∧
        panResultEvents (some sourceResult) = crepHooks.ioEvents targetState) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, _,
      hevents⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact hevents
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact panValuePcResultRel_forbidden_iff structs context exceptionRel
      exceptionCode globalsLookup outcome result returnedClock hrel
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    have hpanAt : panSuccessfulAt panHooks clock ↔
        ∃ sourceOutcome,
          panResultOutcome panHooks (some (outcome, returnedClock)) =
            some sourceOutcome := by
      constructor
      · rintro ⟨result', outcome', heval, houtcome⟩
        rw [hpanClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨sourceOutcome, houtcome⟩
        exact ⟨(outcome, returnedClock), sourceOutcome, hpanClock, houtcome⟩
    have hcrepAt : crepSuccessfulAt crepHooks clock ↔
        ∃ targetOutcome,
          crepResultOutcome
            (crepControlResultToSemantic (some result)) = some targetOutcome := by
      constructor
      · rintro ⟨result', state', outcome', heval, houtcome⟩
        rw [hcrepClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨targetOutcome, houtcome⟩
        exact ⟨crepControlResultToSemantic (some result), state, targetOutcome,
          hcrepClock, houtcome⟩
    rw [hpanAt, hcrepAt]
    exact panValuePcResultRel_success_iff structs context exceptionRel
      exceptionCode globalsLookup panHooks outcome result returnedClock hrel
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    obtain ⟨outcome, returnedClock, result, hsourceResult, htargetResult, hrel,
      _⟩ := hcross sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    subst sourceResult
    subst targetResult
    exact panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock structs context
      exceptionRel exceptionCode globalsLookup panHooks crepHooks hffiOutcome
      sourceClock targetClock outcome returnedClock result targetState
      sourceOutcome targetOutcome hsource htarget hrel hsourceOutcome
      htargetOutcome
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    obtain ⟨_, _, _, _, _, _, hevents⟩ := hcross sourceClock targetClock
      sourceResult sourceOutcome targetResult targetState targetOutcome hsource
      hsourceOutcome htarget htargetOutcome
    exact hevents

/-! ## Connecting the boundary correctness predicate to clocked semantics

The preceding theorem starts from a per-clock `panValuePcResultRel`.  The
original Cake proof obtains that relation by instantiating `pc_compile_correct`
at the source and target evaluator executions.  The witness below keeps that
instantiation explicit: it records the input/output code relations, state
relation, evaluator equations, and the projections from clocked results to
compact `pc` results.  This is intentionally a supported-subset bridge rather
than an assertion that the smaller Flapjack `CrepState` already contains every
field of Cake's richer state relation.
-/

structure PanValuePcSemanticClockEvidence
    {α σ : Type} [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (clock : Nat)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α) where
  sourceInput : PanValuePcInput α
  targetInput : CrepPcInput α
  sourceExecution : PanValuePcExecution α
  targetExecution : CrepPcExecution α
  outcome : PanValueFfiClockOutcome α σ
  returnedClock : Nat
  result : CrepControlResult α
  targetState : CrepState α
  sourceInputStructs : sourceInput.structs = structs
  targetInputStructs : targetInput.structs = structs
  sourceLocalisedCode : panValuePcLocalisedCode sourceInput.code
  programLocalised : localisedProg program
  inputCodeRel : codeRel context sourceInput.code targetInput.code
  inputExcpRel : excpRel context sourceInput.eshapes targetInput.eshapes
  stateRel : panValueCrepStateRel structs context sourceInput.locals
    sourceInput.globals sourceInput.memory targetInput.state
  sourceNotError : sourceExecution.result ≠ .error
  sourceEval : sourceEvaluate context sourceInput program = some sourceExecution
  targetEval : targetEvaluate context targetInput (compileProg context program) =
    some targetExecution
  outputCodeRel : codeRel context sourceExecution.code targetExecution.code
  outputExcpRel : excpRel context sourceExecution.eshapes targetExecution.eshapes
  sourceResult : sourceExecution.result = panOutcomeToPcResult outcome
  targetResult : targetExecution.result = crepControlToPcResult result
  panEval : panHooks.evaluate clock = some (outcome, returnedClock)
  crepEval : crepHooks.evaluate clock =
    (crepControlResultToSemantic (some result), targetState)
  events : panResultEvents (some (outcome, returnedClock)) =
    crepHooks.ioEvents targetState

/-! Build the evidence record at the production clocked-evaluator boundary.
    This constructor fixes both evaluator fields to the executable source and
    Crep adapters above and fixes both observational hooks to their production
    wrappers.  The compiler-correctness, state, code/exception, and event
    premises stay explicit: this theorem packages a real evaluator witness but
    does not turn those obligations into an axiom. -/
def panValuePcSemanticClockEvidence_of_production_adapters
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (clock : Nat)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (sourceState : PanSemEvaluateState α σ)
    (targetFunctions : List (CompiledFunction α))
    (targetPrimitive : CrepPrimitiveHandler α)
    (targetFfi : CrepFfiHandler α)
    (targetSharedMem : CrepSharedMemHandler α)
    (targetBaseAddress targetTopAddress : α)
    (targetState : CrepState α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (sourceExecution : PanValuePcExecution α)
    (targetExecution : CrepPcExecution α)
    (outcome : PanValueFfiClockOutcome α σ) (returnedClock : Nat)
    (result : CrepControlResult α)
    (hsourceInputStructs : sourceInput.structs = structs)
    (htargetInputStructs : targetInput.structs = structs)
    (hsourceLocalisedCode : panValuePcLocalisedCode sourceInput.code)
    (hprogramLocalised : localisedProg program)
    (hinputCodeRel : codeRel context sourceInput.code targetInput.code)
    (hinputExcpRel : excpRel context sourceInput.eshapes targetInput.eshapes)
    (hstateRel : panValueCrepStateRel structs context sourceInput.locals
      sourceInput.globals sourceInput.memory targetInput.state)
    (hsourceNotError : sourceExecution.result ≠ .error)
    (hsource : panValuePcClockedSourceEvaluator clock sourceContext
      sourcePrimitive sourceHandler sourceState context sourceInput program =
      some sourceExecution)
    (htarget : crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive
      targetFfi targetSharedMem targetBaseAddress targetTopAddress context
      targetInput (compileProg context program) = some targetExecution)
    (houtputCodeRel : codeRel context sourceExecution.code targetExecution.code)
    (houtputExcpRel : excpRel context sourceExecution.eshapes
      targetExecution.eshapes)
    (hsourceResult : sourceExecution.result = panOutcomeToPcResult outcome)
    (htargetResult : targetExecution.result = crepControlToPcResult result)
    (hpanEval : (panSemEvaluateHooks sourceContext sourcePrimitive sourceHandler
      sourceState program).evaluate clock = some (outcome, returnedClock))
    (hcrepEval : (crepEvaluateHooks targetFunctions targetPrimitive targetFfi
      targetSharedMem targetBaseAddress targetTopAddress targetState).evaluate
      clock = (crepControlResultToSemantic (some result), targetState))
    (hevents : panResultEvents (some (outcome, returnedClock)) = []) :
    PanValuePcSemanticClockEvidence structs context program clock
      (panValuePcClockedSourceEvaluator clock sourceContext sourcePrimitive
        sourceHandler sourceState)
      (crepPcClockedTargetEvaluator clock targetFunctions targetPrimitive targetFfi
        targetSharedMem targetBaseAddress targetTopAddress)
      codeRel excpRel exceptionRel exceptionCode globalsLookup
      (panSemEvaluateHooks sourceContext sourcePrimitive sourceHandler sourceState
        program)
      (crepEvaluateHooks targetFunctions targetPrimitive targetFfi targetSharedMem
        targetBaseAddress targetTopAddress targetState) := by
  refine {
    sourceInput := sourceInput
    targetInput := targetInput
    sourceExecution := sourceExecution
    targetExecution := targetExecution
    outcome := outcome
    returnedClock := returnedClock
    result := result
    targetState := targetState
    sourceInputStructs := hsourceInputStructs
    targetInputStructs := htargetInputStructs
    sourceLocalisedCode := hsourceLocalisedCode
    programLocalised := hprogramLocalised
    inputCodeRel := hinputCodeRel
    inputExcpRel := hinputExcpRel
    stateRel := hstateRel
    sourceNotError := hsourceNotError
    sourceEval := hsource
    targetEval := htarget
    outputCodeRel := houtputCodeRel
    outputExcpRel := houtputExcpRel
    sourceResult := hsourceResult
    targetResult := htargetResult
    panEval := hpanEval
    crepEval := hcrepEval
    events := ?_ }
  simpa [crepEvaluateHooks] using hevents

/-! Preserve the full context-coded `pc_compile_correct` result at one clock.
    This is the evaluator boundary used by the declaration induction: all
    source/target state, localisation, evaluator, and post-code premises remain
    visible, while the exception-code and global-lookup evidence is retained. -/
theorem PanValuePcSemanticClockEvidence.resultRelWithContextCode
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult evidence.outcome)
      (crepControlToPcResult evidence.result) := by
  have hrel := hcorrect context structs evidence.sourceInput
    evidence.targetInput exceptionRel evidence.sourceExecution
    evidence.targetExecution evidence.sourceInputStructs
    evidence.targetInputStructs evidence.sourceLocalisedCode
    evidence.programLocalised evidence.inputCodeRel evidence.inputExcpRel
    evidence.stateRel evidence.sourceNotError evidence.sourceEval
    evidence.targetEval evidence.outputCodeRel evidence.outputExcpRel
  rw [evidence.sourceResult, evidence.targetResult] at hrel
  exact hrel

/-! Dispatch one clocked evaluator evidence through the two ordinary
    `state_rel_imp_semantics_to_crep` result branches.  The returned context
    state relation and arbitrary Raise lookup are extracted from the
    context-coded compiler result rather than assumed separately. -/
theorem PanValuePcSemanticClockEvidence.normalOrRaisedResultRelWithContextCode_of_branch
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      evidence.sourceInput.locals evidence.sourceInput.globals
      evidence.sourceInput.memory evidence.targetInput.state)
    (hbranch :
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        evidence.outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        evidence.result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        evidence.outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        evidence.result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult evidence.outcome)
      (crepControlToPcResult evidence.result) ∧
    ∃ sourceLocals sourceGlobals sourceMemory targetState,
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, _⟩
  have hrel := PanValuePcSemanticClockEvidence.resultRelWithContextCode
    hcorrect evidenceClock evidence
  rcases hbranch with hnormal | hraised
  · rcases hnormal with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      targetState, houtcome, hresult⟩
    have hnormalRel :
        panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
          globalsLookup
          (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) := by
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hrel
    have hstate := (panValuePcResultRelWithContextCode_normal_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
      targetState).1 hnormalRel
    exact ⟨hrel,
      ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
        ⟨hoverlap, hmax, hstate⟩⟩⟩
  · rcases hraised with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      sourceException, sourceValue, targetState, targetException, houtcome, hresult,
      hlookup⟩
    have hraisedRel :
        panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
          globalsLookup
          (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
          (.raised targetState targetException) := by
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hrel
    have hstate := (panValuePcResultRelWithContextCode_raised_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException).1 hraisedRel
    exact ⟨hrel,
      ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
        ⟨hoverlap, hmax, hstate.1⟩⟩⟩

theorem PanValuePcSemanticClockEvidence.resultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate
      targetEvaluate codeRel excpRel exceptionRel exceptionCode globalsLookup
      panHooks crepHooks) :
    panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult evidence.outcome)
      (crepControlToPcResult evidence.result) := by
  have hrel := hcorrect context structs evidence.sourceInput
    evidence.targetInput exceptionRel evidence.sourceExecution
    evidence.targetExecution evidence.sourceInputStructs
    evidence.targetInputStructs evidence.sourceLocalisedCode
    evidence.programLocalised evidence.inputCodeRel evidence.inputExcpRel
    evidence.stateRel evidence.sourceNotError evidence.sourceEval
    evidence.targetEval evidence.outputCodeRel evidence.outputExcpRel
  rw [evidence.sourceResult, evidence.targetResult] at hrel
  exact hrel

theorem PanValuePcSemanticClockEvidence.semanticOutcomeRel_withContextCode
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceOutcome : PanSemanticOutcome)
    (targetOutcome : CrepSemanticOutcome)
    (hsourceOutcome : panResultOutcome panHooks
      (some (evidence.outcome, evidence.returnedClock)) = some sourceOutcome)
    (htargetOutcome : crepResultOutcome
      (crepControlResultToSemantic (some evidence.result)) = some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  exact panValuePcResultRel_semanticOutcomeRel_of_outcome
    structs context exceptionRel exceptionCode globalsLookup panHooks hffiOutcome
    evidence.outcome evidence.result evidence.returnedClock sourceOutcome
    targetOutcome
    (PanValuePcSemanticClockEvidence.resultRel
      (panValuePcCompileCorrect_of_withContextCode sourceEvaluate targetEvaluate
        codeRel excpRel exceptionCode globalsLookup program hcorrect)
      evidenceClock evidence)
    hsourceOutcome htargetOutcome

/-! The returned-call branch of Cake's `state_rel_imp_semantics_to_crep`
    carries a concrete source/target evaluator result, rather than merely
    asserting that both observations are successful.  This specialization
    exposes that branch as a semantic outcome relation: the compiler
    correctness theorem supplies the result relation, while the returned
    constructors discharge the two success observations definitionally. -/
theorem PanValuePcSemanticClockEvidence.returnedSemanticOutcomeRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α)
    (houtcome : evidence.outcome =
      .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi sourceValues))
    (hresult : evidence.result = .returned targetState targetValues) :
    panCrepSemanticOutcomeRel .success .success := by
  have hsourceOutcome :
      panResultOutcome panHooks
        (some (evidence.outcome, evidence.returnedClock)) = some .success := by
    rw [houtcome]
    simp [panResultOutcome]
  have htargetOutcome :
      crepResultOutcome
        (crepControlResultToSemantic (some evidence.result)) = some .success := by
    rw [hresult]
    simp [crepResultOutcome, crepControlResultToSemantic]
  exact PanValuePcSemanticClockEvidence.semanticOutcomeRel_withContextCode
    hcorrect evidenceClock evidence hffiOutcome .success .success hsourceOutcome
    htargetOutcome

/-! The terminal FFI branch of Cake's `state_rel_imp_semantics_decls_to_crep`
    has a concrete observable outcome as well.  The result relation supplies
    equality of the final event, while the source hook law identifies the
    source observation with that event's semantic outcome. -/
theorem PanValuePcSemanticClockEvidence.finalFfiSemanticOutcomeRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (houtcome : evidence.outcome =
      .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceEvent))
    (hresult : evidence.result = .finalFfi targetState targetEvent) :
    panCrepSemanticOutcomeRel (.ffi sourceEvent.outcome)
      (.ffi targetEvent.outcome) := by
  have hsourceOutcome :
      panResultOutcome panHooks
        (some (evidence.outcome, evidence.returnedClock)) =
        some (.ffi sourceEvent.outcome) := by
    rw [houtcome]
    simp [panResultOutcome, hffiOutcome]
  have htargetOutcome :
      crepResultOutcome
        (crepControlResultToSemantic (some evidence.result)) =
        some (.ffi targetEvent.outcome) := by
    rw [hresult]
    simp [crepResultOutcome, crepControlResultToSemantic]
  exact PanValuePcSemanticClockEvidence.semanticOutcomeRel_withContextCode
    hcorrect evidenceClock evidence hffiOutcome (.ffi sourceEvent.outcome)
    (.ffi targetEvent.outcome) hsourceOutcome htargetOutcome

/-! The non-success counterpart of `returnedSemanticOutcomeRel`. Cake's
    `state_rel_imp_semantics_to_crep` induction has separate normal, raised,
    and clock-exhaustion cases, but all three are transported by the same
    result relation before the observational semantics classifies them as a
    forbidden run. Keep the evaluator equations and state relation inside
    `evidence`: this is a real composition bridge, not a premise-only alias
    for `panValuePcResultRel_forbidden_iff`. -/
theorem PanValuePcSemanticClockEvidence.forbiddenResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks) :
    panForbiddenResult
        (some (evidence.outcome, evidence.returnedClock)) ↔
      crepForbiddenResult
        (crepControlResultToSemantic (some evidence.result)) := by
  apply panValuePcResultRel_forbidden_iff structs context exceptionRel
    exceptionCode globalsLookup evidence.outcome evidence.result
    evidence.returnedClock
  exact PanValuePcSemanticClockEvidence.resultRel
    (panValuePcCompileCorrect_of_withContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program hcorrect)
    evidenceClock evidence

theorem PanValuePcSemanticClockEvidence.raisedForbiddenResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (houtcome : evidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : evidence.result = .raised targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    (panForbiddenResult (some (evidence.outcome, evidence.returnedClock)) ↔
      crepForbiddenResult (crepControlResultToSemantic (some evidence.result))) := by
  have hrel := PanValuePcSemanticClockEvidence.resultRel
    (panValuePcCompileCorrect_of_withContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program hcorrect)
    evidenceClock evidence
  rw [houtcome, hresult] at hrel
  have hraisedRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) := by
    simpa [panOutcomeToPcResult, crepControlToPcResult] using hrel
  have hforbidden := panValuePcResultRel_forbidden_iff
    structs context exceptionRel exceptionCode globalsLookup
    (.control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
      sourceException sourceValue))
    (.raised targetState targetException) evidence.returnedClock hraisedRel
  exact ⟨hraisedRel, by simpa [houtcome, hresult] using hforbidden⟩

/-! The normal-control branch of Cake's
    `state_rel_imp_semantics_to_crep` induction keeps the evaluator and state
    relation explicit even though neither observation is a successful
    termination.  It transports the normal result relation and the forbidden
    observation classification together. -/
theorem PanValuePcSemanticClockEvidence.normalForbiddenResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : evidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : evidence.result = .normal targetState) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) ∧
    (panForbiddenResult (some (evidence.outcome, evidence.returnedClock)) ↔
      crepForbiddenResult (crepControlResultToSemantic (some evidence.result))) := by
  have hrel := PanValuePcSemanticClockEvidence.resultRel
    (panValuePcCompileCorrect_of_withContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program hcorrect)
    evidenceClock evidence
  rw [houtcome, hresult] at hrel
  have hnormalRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.normal sourceLocals sourceGlobals sourceMemory)
        (.normal targetState) := by
    simpa [panOutcomeToPcResult, crepControlToPcResult] using hrel
  have hforbidden := panValuePcResultRel_forbidden_iff
    structs context exceptionRel exceptionCode globalsLookup
    (.control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (.normal targetState) evidence.returnedClock hnormalRel
  exact ⟨hnormalRel, by simpa [houtcome, hresult] using hforbidden⟩

/-! The cross-clock Raise case of Cake's semantic induction.  Both clock
    witnesses retain their evaluator equations and code/state relations; the
    result relation then transports the fact that neither raised observation
    is a successful semantic result. -/
theorem PanValuePcSemanticClockEvidence.crossClockRaisedForbiddenResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (houtcome : sourceEvidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : targetEvidence.result = .raised targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    (panForbiddenResult
        (some (sourceEvidence.outcome, sourceEvidence.returnedClock)) ↔
      crepForbiddenResult
        (crepControlResultToSemantic (some targetEvidence.result))) := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  have hraisedRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) := by
    have hcontext := panValuePcResultRel_of_withContextCode structs context
      exceptionRel exceptionCode globalsLookup
      (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) hrel
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hcontext
  have hforbidden := panValuePcResultRel_forbidden_iff
    structs context exceptionRel exceptionCode globalsLookup
    (.control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
      sourceException sourceValue))
    (.raised targetState targetException) sourceEvidence.returnedClock hraisedRel
  exact ⟨hraisedRel, by simpa [houtcome, hresult] using hforbidden⟩

/-! The cross-clock Raise branch also preserves Cake's strengthened context
    relation.  This is the arbitrary-payload state step for
    `state_rel_imp_semantics_to_crep`: the compiler theorem still supplies all
    evaluator, code, exception, and state premises, while the result relation
    retains the raised payload/global lookup evidence. -/
theorem PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_withContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (hoverlap : panValueNoOverlap context.vars)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    (houtcome : sourceEvidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : targetEvidence.result = .raised targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  have hraisedRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) := by
    have hcontext := panValuePcResultRel_of_withContextCode structs context
      exceptionRel exceptionCode globalsLookup
      (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) hrel
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hcontext
  exact ⟨hraisedRel, ⟨hoverlap, hmax, hraisedRel.1⟩⟩

/-! Consume the bundled Cake state relation for the arbitrary-payload Raise
    branch.  The declaration induction can therefore pass one state package
    while retaining the evaluator, exception lookup, and result premises. -/
theorem PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (houtcome : sourceEvidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : targetEvidence.result = .raised targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, hstateRel⟩
  exact PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_withContext
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel hstateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceException sourceValue targetState targetException
    hoverlap hmax houtcome hresult

/-! Retain the exception-table lookup component when the cross-clock Raise
    relation is consumed by the declaration induction.  The base relation is
    sufficient for the compact result case, but Cake's context-coded branch
    also carries the explicit exception lookup premise. -/
theorem PanValuePcSemanticClockEvidence.crossClockRaisedResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (houtcome : sourceEvidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : targetEvidence.result = .raised targetState targetException)
    (hlookup : lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_of_stateRelWithContext
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel inputStateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceException sourceValue targetState targetException
    houtcome hresult with ⟨hrel, hstate⟩
  exact ⟨panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
    structs context exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hrel hlookup,
    hstate⟩

/-! Consume Cake's complete arbitrary-Raise package at the cross-clock boundary.
    Unlike the lookup-only adapter above, this theorem retains the explicit
    flattened global-store and output-state evidence carried by
    `panValuePcRaisedHraiseData`; evaluator, input-state, result, and exception
    premises remain visible to the declaration induction. -/
theorem PanValuePcSemanticClockEvidence.crossClockRaisedResultRelWithContextCode_of_hraiseData
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (hraiseData : panValuePcRaisedHraiseData exceptionCode globalsLookup
      structs context exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (houtcome : sourceEvidence.outcome =
      .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceException sourceValue))
    (hresult : targetEvidence.result = .raised targetState targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, hstateRel⟩
  have hbase := PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_withContext
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel hstateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceException sourceValue targetState targetException
    hoverlap hmax houtcome hresult
  have hcontext := panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
    structs context exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hbase.1
    hraiseData.2
  exact ⟨hcontext, ⟨hoverlap, hmax, hraiseData.1.1⟩⟩

/-! The cross-clock normal-control branch of Cake's semantic induction.
    Normal results are forbidden observations, but unlike the generic
    forbidden wrapper this theorem exposes the concrete source/target states
    and re-applies `pc_compile_correct` across the two clock witnesses. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalForbiddenResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : sourceEvidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : targetEvidence.result = .normal targetState) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) ∧
    (panForbiddenResult
        (some (sourceEvidence.outcome, sourceEvidence.returnedClock)) ↔
      crepForbiddenResult
        (crepControlResultToSemantic (some targetEvidence.result))) := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  have hnormalRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.normal sourceLocals sourceGlobals sourceMemory)
        (.normal targetState) := by
    have hcontext := panValuePcResultRel_of_withContextCode structs context
      exceptionRel exceptionCode globalsLookup
      sourceEvidence.sourceExecution.result targetEvidence.targetExecution.result hrel
    rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hcontext
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hcontext
  have hforbidden := panValuePcResultRel_forbidden_iff
    structs context exceptionRel exceptionCode globalsLookup
    (.control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (.normal targetState) sourceEvidence.returnedClock hnormalRel
  exact ⟨hnormalRel, by simpa [houtcome, hresult] using hforbidden⟩

/-! Reapply `pc_compile_correct` across two clock witnesses. This is the
source/target execution step used by Cake's `evaluate_add_clock_eq` cases: the
clocked evaluator monotonicity itself is not assumed here, but every
cross-clock code, exception, state, and output relation remains explicit. -/
theorem PanValuePcSemanticClockEvidence.crossResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  exact hrel

theorem PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  exact panValuePcResultRel_of_withContextCode structs context exceptionRel
    exceptionCode globalsLookup _ _ hrel

/-! Relate source evidence and target evidence whose evaluator clocks differ.
    The existing same-record bridge requires one evaluator pair; this pairwise
    form is the production adapter boundary used by the clock-indexed semantic
    induction. -/
theorem panValuePcResultRelWithContextCode_of_clocked_evidence_pair
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : Nat → PanValuePcEvaluator α}
    {targetEvaluate : Nat → CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (sourceClock targetClock : Nat)
    (hcorrect : PanValuePcCompileCorrectWithContextCode
      (sourceEvaluate sourceClock) (targetEvaluate targetClock)
      codeRel excpRel exceptionCode globalsLookup program)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock (sourceEvaluate sourceClock) (targetEvaluate sourceClock)
      codeRel excpRel exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock (sourceEvaluate targetClock) (targetEvaluate targetClock)
      codeRel excpRel exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel stateRel
    sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  exact hrel

/-! Compose clock-indexed production evidence when the compact evaluator itself
    is fixed at each clock.  This is the missing top-level shape for the
    production adapters: every source/target evaluator pair gets its own
    explicit `pc_compile_correct` premise, while input/output code relations,
    state relations, result constructors, and event equalities remain visible.
    The theorem therefore does not identify clocked evaluators or discharge
    arbitrary Raise evidence implicitly. -/
theorem panCrepSemanticAgreement_of_clocked_pcCompileCorrectWithContextCode
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : Nat → PanValuePcEvaluator α)
    (targetEvaluate : Nat → CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : ∀ (sourceClock targetClock : Nat),
      PanValuePcCompileCorrectWithContextCode
        (sourceEvaluate sourceClock) (targetEvaluate targetClock)
        codeRel excpRel exceptionCode globalsLookup program)
    (sourceEvidence : ∀ clock : Nat,
      PanValuePcSemanticClockEvidence structs context program clock
        (sourceEvaluate clock) (targetEvaluate clock) codeRel excpRel
        exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : ∀ clock : Nat,
      PanValuePcSemanticClockEvidence structs context program clock
        (sourceEvaluate clock) (targetEvaluate clock) codeRel excpRel
        exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (sourceEvidence sourceClock).sourceInput.code
        (targetEvidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (sourceEvidence sourceClock).sourceInput.eshapes
        (targetEvidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (sourceEvidence sourceClock).sourceInput.locals
        (sourceEvidence sourceClock).sourceInput.globals
        (sourceEvidence sourceClock).sourceInput.memory
        (targetEvidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (sourceEvidence sourceClock).sourceExecution.code
        (targetEvidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (sourceEvidence sourceClock).sourceExecution.eshapes
        (targetEvidence targetClock).targetExecution.eshapes)
    (heventsCross : ∀ (sourceClock targetClock : Nat),
      panResultEvents (some ((sourceEvidence sourceClock).outcome,
        (sourceEvidence sourceClock).returnedClock)) =
        crepHooks.ioEvents (targetEvidence targetClock).targetState) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcResultRel_pair_cross_clock structs context
    exceptionRel exceptionCode globalsLookup panHooks crepHooks hffiOutcome
  · intro clock
    let sourceEvidenceClock := sourceEvidence clock
    let targetEvidenceClock := targetEvidence clock
    refine ⟨sourceEvidenceClock.outcome, sourceEvidenceClock.returnedClock,
      targetEvidenceClock.result, targetEvidenceClock.targetState,
      sourceEvidenceClock.panEval, targetEvidenceClock.crepEval, ?_, ?_⟩
    · exact panValuePcResultRel_of_withContextCode structs context exceptionRel
        exceptionCode globalsLookup _ _
        (panValuePcResultRelWithContextCode_of_clocked_evidence_pair
          clock clock (hcorrect clock clock) sourceEvidenceClock targetEvidenceClock
          (hinputCodeRel clock clock) (hinputExcpRel clock clock)
          (hinputStateRel clock clock) (houtputCodeRel clock clock)
          (houtputExcpRel clock clock))
    · exact heventsCross clock clock
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    let sourceEvidenceClock := sourceEvidence sourceClock
    let targetEvidenceClock := targetEvidence targetClock
    have hsourceResult : sourceResult =
        (sourceEvidenceClock.outcome, sourceEvidenceClock.returnedClock) := by
      apply Option.some.inj
      exact hsource.symm.trans sourceEvidenceClock.panEval
    have htargetPair : (targetResult, targetState) =
        (crepControlResultToSemantic (some targetEvidenceClock.result),
          targetEvidenceClock.targetState) :=
      htarget.symm.trans targetEvidenceClock.crepEval
    have htargetResult : targetResult =
        crepControlResultToSemantic (some targetEvidenceClock.result) :=
      congrArg Prod.fst htargetPair
    have htargetState : targetState = targetEvidenceClock.targetState :=
      congrArg Prod.snd htargetPair
    refine ⟨sourceEvidenceClock.outcome, sourceEvidenceClock.returnedClock,
      targetEvidenceClock.result, hsourceResult, htargetResult, ?_, ?_⟩
    · exact panValuePcResultRel_of_withContextCode structs context exceptionRel
        exceptionCode globalsLookup _ _
        (panValuePcResultRelWithContextCode_of_clocked_evidence_pair
          sourceClock targetClock (hcorrect sourceClock targetClock)
          sourceEvidenceClock targetEvidenceClock
          (hinputCodeRel sourceClock targetClock)
          (hinputExcpRel sourceClock targetClock)
          (hinputStateRel sourceClock targetClock)
          (houtputCodeRel sourceClock targetClock)
          (houtputExcpRel sourceClock targetClock))
    · simpa [hsourceResult, htargetState] using
        heventsCross sourceClock targetClock

/-! The cross-clock terminal-FFI branch of the semantic induction.  It
    preserves the final event across the source and target clocks before
    projecting the related result to its observable FFI outcome. -/
theorem PanValuePcSemanticClockEvidence.crossClockFinalFfiSemanticOutcomeRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (houtcome : sourceEvidence.outcome =
      .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceEvent))
    (hresult : targetEvidence.result = .finalFfi targetState targetEvent) :
    panCrepSemanticOutcomeRel (.ffi sourceEvent.outcome)
      (.ffi targetEvent.outcome) := by
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel
  have hsourceOutcome :
      panResultOutcome panHooks
        (some (sourceEvidence.outcome, sourceEvidence.returnedClock)) =
        some (.ffi sourceEvent.outcome) := by
    rw [houtcome]
    simp [panResultOutcome, hffiOutcome]
  have htargetOutcome :
      crepResultOutcome
        (crepControlResultToSemantic (some targetEvidence.result)) =
        some (.ffi targetEvent.outcome) := by
    rw [hresult]
    simp [crepResultOutcome, crepControlResultToSemantic]
  exact panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock
    structs context exceptionRel exceptionCode globalsLookup panHooks crepHooks
    hffiOutcome sourceClock targetClock sourceEvidence.outcome
    sourceEvidence.returnedClock targetEvidence.result targetEvidence.targetState
    (.ffi sourceEvent.outcome) (.ffi targetEvent.outcome)
    sourceEvidence.panEval targetEvidence.crepEval hrel
    hsourceOutcome htargetOutcome

/-! The cross-clock returned branch of the semantic induction.  Unlike the
    same-clock convenience theorem, this consumes both evaluator equations and
    the cross-clock input/output relations before exposing the successful
    semantic outcome. -/
theorem PanValuePcSemanticClockEvidence.crossClockReturnedSemanticOutcomeRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α)
    (houtcome : sourceEvidence.outcome =
      .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceValues))
    (hresult : targetEvidence.result = .returned targetState targetValues) :
    panCrepSemanticOutcomeRel .success .success := by
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel
  have hsourceOutcome :
      panResultOutcome panHooks
        (some (sourceEvidence.outcome, sourceEvidence.returnedClock)) =
        some .success := by
    rw [houtcome]
    simp [panResultOutcome]
  have htargetOutcome :
      crepResultOutcome
        (crepControlResultToSemantic (some targetEvidence.result)) =
        some .success := by
    rw [hresult]
    simp [crepResultOutcome, crepControlResultToSemantic]
  exact panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock
    structs context exceptionRel exceptionCode globalsLookup panHooks crepHooks
    hffiOutcome sourceClock targetClock sourceEvidence.outcome
    sourceEvidence.returnedClock targetEvidence.result targetEvidence.targetState
    .success .success sourceEvidence.panEval targetEvidence.crepEval hrel
    hsourceOutcome htargetOutcome

/-! The returned-result counterpart of the cross-clock semantic branch.  This
    keeps the concrete flattened values and related target state available to
    the caller instead of projecting immediately to `.success`; it is the
    result-relation step consumed by Cake's returned-call induction. -/
theorem PanValuePcSemanticClockEvidence.crossClockReturnedResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α)
    (houtcome : sourceEvidence.outcome =
      .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceValues))
    (hresult : targetEvidence.result = .returned targetState targetValues) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned targetState targetValues) := by
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel
  simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
    using hrel

/-! The returned branch retains Cake's strengthened context in addition to the
    flattened value relation.  This is the returned-result state step consumed
    by the declaration induction, with all cross-clock evaluator and code
    relations still explicit. -/
theorem PanValuePcSemanticClockEvidence.crossClockReturnedResultRel_withContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α)
    (hoverlap : panValueNoOverlap context.vars)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    (houtcome : sourceEvidence.outcome =
      .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceValues))
    (hresult : targetEvidence.result = .returned targetState targetValues) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned targetState targetValues) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  have hresultRel := PanValuePcSemanticClockEvidence.crossClockReturnedResultRel
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceValues targetState targetValues houtcome hresult
  exact ⟨hresultRel, ⟨hoverlap, hmax, hresultRel.1⟩⟩

/-! Consume the bundled Cake state relation for the returned-call branch while
    retaining its context-coded value relation.  This is the declaration
    induction shape for returned results, with evaluator and result premises
    kept explicit rather than projected into a compatibility predicate. -/
theorem PanValuePcSemanticClockEvidence.crossClockReturnedResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α)
    (houtcome : sourceEvidence.outcome =
      .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceValues))
    (hresult : targetEvidence.result = .returned targetState targetValues) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned targetState targetValues) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, hstateRel⟩
  have hresultRel := PanValuePcSemanticClockEvidence.crossClockReturnedResultRel
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel hstateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceValues targetState targetValues houtcome hresult
  have hparts := (panValuePcResultRel_returned_iff structs context exceptionRel
    exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory sourceValues
    targetState targetValues).1 hresultRel
  exact ⟨(panValuePcResultRelWithContextCode_returned_iff structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
    sourceValues targetState targetValues).2 hparts,
    ⟨hoverlap, hmax, hparts.1⟩⟩

/-! The declaration-boundary FinalFFI branch keeps both the final event and the
    strengthened Cake state relation.  The event equality is retained rather
    than hidden behind the observational outcome, so this bridge can be used
    directly by the declaration induction. -/
theorem PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (houtcome : sourceEvidence.outcome =
      .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceEvent))
    (hresult : targetEvidence.result = .finalFfi targetState targetEvent) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent)
      (.finalFfi targetState targetEvent) := by
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel
  simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
    using hrel

/-! Consume the full Cake state package for the FinalFFI declaration case.
    This is the state-relation instantiation used after the returned and
    normal-call branches: evaluator, code, state, result, and final-event
    premises all remain explicit. -/
theorem PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent)
    (houtcome : sourceEvidence.outcome =
      .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
        sourceEvent))
    (hresult : targetEvidence.result = .finalFfi targetState targetEvent) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent)
      (.finalFfi targetState targetEvent) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, hstateRel⟩
  have hresultRel := PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRel
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel hstateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi sourceEvent targetState targetEvent houtcome hresult
  have hparts := (panValuePcResultRel_finalFfi_iff structs context exceptionRel
    exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory sourceEvent
    targetState targetEvent).1 hresultRel
  exact ⟨(panValuePcResultRelWithContextCode_finalFfi_iff structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
    sourceEvent targetState targetEvent).2 hparts,
    ⟨hoverlap, hmax, hparts.1⟩⟩

/-! The normal-result counterpart of the cross-clock semantic branch.  This is
    the ordinary call case of Cake's declaration induction: evaluator and
    state evidence are retained, while the result is projected without
    weakening the explicit code and exception premises. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalResultRel
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : sourceEvidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : targetEvidence.result = .normal targetState) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) := by
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel
  simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
    using hrel

/-! Package the normal-call result with Cake's strengthened state relation.
    The two context invariants are explicit because the top-level
    `state_rel_imp_semantics_to_crep` induction consumes them separately from
    the ordinary source/target state fields. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalResultRel_withContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (stateRel : panValueCrepStateRel structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (hoverlap : panValueNoOverlap context.vars)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    (houtcome : sourceEvidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : targetEvidence.result = .normal targetState) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) ∧
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  have hresultRel := PanValuePcSemanticClockEvidence.crossClockNormalResultRel
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel stateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi targetState houtcome hresult
  have houtputRel := (panValuePcResultRel_normal_iff structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory targetState).1 hresultRel
  exact ⟨hresultRel, ⟨hoverlap, hmax, houtputRel⟩⟩

/-! Consume the bundled Cake state relation at the normal-call boundary.  This
    is the declaration-induction shape used by `state_rel_imp_semantics_to_crep`:
    the input evaluator witnesses and result constructors stay explicit, while
    the no-overlap and context-max premises are obtained from one state-relation
    hypothesis rather than reconstructed by the caller. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalResultRel_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : sourceEvidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : targetEvidence.result = .normal targetState) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) ∧
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  rcases inputStateRel with ⟨hoverlap, hmax, hstateRel⟩
  exact PanValuePcSemanticClockEvidence.crossClockNormalResultRel_withContext
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel hstateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi targetState hoverlap hmax houtcome hresult

/-! Preserve the strengthened context-coded relation at the normal-call
    boundary.  This is the normal counterpart of the arbitrary Raise bridge:
    evaluator, code, state, and result premises remain visible while the
    declaration induction receives the full context relation. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : sourceEvidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : targetEvidence.result = .normal targetState) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  rcases PanValuePcSemanticClockEvidence.crossClockNormalResultRel_of_stateRelWithContext
    hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
    inputExcpRel inputStateRel outputCodeRel outputExcpRel sourceLocals sourceGlobals
    sourceMemory sourceFfi targetState houtcome hresult with ⟨_, hstate⟩
  rcases hstate with ⟨hoverlap, hmax, hbase⟩
  exact ⟨(panValuePcResultRelWithContextCode_normal_iff structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
    targetState).2 hbase, ⟨hoverlap, hmax, hbase⟩⟩

/-! The same-clock normal-call instantiation is the direct declaration step of
    `state_rel_imp_semantics_to_crep`.  Keep the evaluator, state, and result
    constructors explicit while specializing the cross-clock bridge to one
    source/target clock. -/
theorem PanValuePcSemanticClockEvidence.normalResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program
      clock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context evidence.sourceInput.code
      evidence.targetInput.code)
    (inputExcpRel : excpRel context evidence.sourceInput.eshapes
      evidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      evidence.sourceInput.locals evidence.sourceInput.globals
      evidence.sourceInput.memory evidence.targetInput.state)
    (outputCodeRel : codeRel context evidence.sourceExecution.code
      evidence.targetExecution.code)
    (outputExcpRel : excpRel context evidence.sourceExecution.eshapes
      evidence.targetExecution.eshapes)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceFfi : FfiState σ)
    (targetState : CrepState α)
    (houtcome : evidence.outcome =
      .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi))
    (hresult : evidence.result = .normal targetState) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) ∧
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
  exact PanValuePcSemanticClockEvidence.crossClockNormalResultRelWithContextCode_of_stateRelWithContext
    hcorrect clock clock evidence evidence inputCodeRel inputExcpRel inputStateRel
    outputCodeRel outputExcpRel sourceLocals sourceGlobals sourceMemory sourceFfi
    targetState houtcome hresult

/-! Dispatch the two ordinary declaration-induction branches at arbitrary
    source and target clocks.  The branch witness is explicit: normal results
    carry only the state relation, while raised results additionally carry the
    exception-table lookup required by the context-coded relation. -/
theorem PanValuePcSemanticClockEvidence.crossClockNormalOrRaisedResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (hbranch :
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        sourceEvidence.outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        targetEvidence.result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        sourceEvidence.outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        targetEvidence.result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult sourceEvidence.outcome)
      (crepControlToPcResult targetEvidence.result) ∧
    ∃ sourceLocals sourceGlobals sourceMemory targetState,
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  rcases hbranch with hnormal | hraised
  · rcases hnormal with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      targetState, houtcome, hresult⟩
    have hnormalRel :=
      PanValuePcSemanticClockEvidence.crossClockNormalResultRelWithContextCode_of_stateRelWithContext
        hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
        inputExcpRel inputStateRel outputCodeRel outputExcpRel sourceLocals
        sourceGlobals sourceMemory sourceFfi targetState houtcome hresult
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      hnormalRel.2⟩⟩
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hnormalRel.1
  · rcases hraised with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      sourceException, sourceValue, targetState, targetException, houtcome,
      hresult, hlookup⟩
    have hraisedRel :=
      PanValuePcSemanticClockEvidence.crossClockRaisedResultRelWithContextCode_of_stateRelWithContext
        hcorrect sourceClock targetClock sourceEvidence targetEvidence inputCodeRel
        inputExcpRel inputStateRel outputCodeRel outputExcpRel sourceLocals
        sourceGlobals sourceMemory sourceFfi sourceException sourceValue targetState
        targetException houtcome hresult hlookup
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      hraisedRel.2⟩⟩
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hraisedRel.1

/-! Lift the branch dispatcher over the arbitrary clock family used by
    `state_rel_imp_semantics_to_crep`.  This is the result-relation half of the
    top-level evaluator instantiation: all per-clock input/output relations
    and the constructor witness remain arguments, while the theorem supplies
    the context-coded result relation for every clock pair. -/
theorem panValuePcResultRelWithContextCode_of_pairwise_normalOrRaised_evidence
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ clock : Nat,
      PanValuePcSemanticClockEvidence structs context program clock
        sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
        globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hbranch : ∀ (sourceClock targetClock : Nat),
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)) :
    ∀ (sourceClock targetClock : Nat),
      panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
        globalsLookup (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result) ∧
      ∃ sourceLocals sourceGlobals sourceMemory targetState,
        panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
          sourceMemory targetState := by
  intro sourceClock targetClock
  exact PanValuePcSemanticClockEvidence.crossClockNormalOrRaisedResultRelWithContextCode_of_stateRelWithContext
    hcorrect sourceClock targetClock (hevidence sourceClock) (hevidence targetClock)
    (hinputCodeRel sourceClock targetClock) (hinputExcpRel sourceClock targetClock)
    (hinputStateRel sourceClock targetClock)
    (houtputCodeRel sourceClock targetClock) (houtputExcpRel sourceClock targetClock)
    (hbranch sourceClock targetClock)

/-! Generalize the normal/raised result bridge to the clocked production
    evaluator family.  Cake's top-level induction compares a source evaluator
    fixed at one clock with a target evaluator fixed at another; this adapter
    keeps that pairwise `pc_compile_correct` premise visible instead of
    collapsing the family to one evaluator pair. -/
theorem panValuePcResultRelWithContextCode_of_clocked_normalOrRaised_evidence
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    (sourceEvaluate : Nat → PanValuePcEvaluator α)
    (targetEvaluate : Nat → CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : ∀ (sourceClock targetClock : Nat),
      PanValuePcCompileCorrectWithContextCode
        (sourceEvaluate sourceClock) (targetEvaluate targetClock)
        codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat),
      PanValuePcSemanticClockEvidence structs context program clock
        (sourceEvaluate clock) (targetEvaluate clock) codeRel excpRel
        exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hbranch : ∀ (sourceClock targetClock : Nat),
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)) :
    ∀ (sourceClock targetClock : Nat),
      panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
        globalsLookup (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result) ∧
      ∃ sourceLocals sourceGlobals sourceMemory targetState,
        panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
          sourceMemory targetState := by
  intro sourceClock targetClock
  have hresult := panValuePcResultRelWithContextCode_of_clocked_evidence_pair
    sourceClock targetClock (hcorrect sourceClock targetClock)
    (hevidence sourceClock) (hevidence targetClock)
    (hinputCodeRel sourceClock targetClock)
    (hinputExcpRel sourceClock targetClock)
    (hinputStateRel sourceClock targetClock).2.2
    (houtputCodeRel sourceClock targetClock)
    (houtputExcpRel sourceClock targetClock)
  rcases hbranch sourceClock targetClock with hnormal | hraised
  · rcases hnormal with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      targetState, houtcome, htarget⟩
    have hnormalResult :
        panValuePcResultRelWithContextCode structs context exceptionRel
          exceptionCode globalsLookup
          (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) := by
      simpa [houtcome, htarget, panOutcomeToPcResult, crepControlToPcResult]
        using hresult
    have hstate := (panValuePcResultRelWithContextCode_normal_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
      sourceMemory targetState).1 hnormalResult
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      ⟨(hinputStateRel sourceClock targetClock).1,
        (hinputStateRel sourceClock targetClock).2.1, hstate⟩⟩⟩
    simpa [houtcome, htarget, panOutcomeToPcResult, crepControlToPcResult]
      using hnormalResult
  · rcases hraised with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      sourceException, sourceValue, targetState, targetException, houtcome,
      htarget, hlookup⟩
    have hraisedResult :
        panValuePcResultRelWithContextCode structs context exceptionRel
          exceptionCode globalsLookup
          (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
          (.raised targetState targetException) := by
      simpa [houtcome, htarget, panOutcomeToPcResult, crepControlToPcResult]
        using hresult
    have hstate := (panValuePcResultRelWithContextCode_raised_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException).1
      hraisedResult
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      ⟨(hinputStateRel sourceClock targetClock).1,
        (hinputStateRel sourceClock targetClock).2.1, hstate.1⟩⟩⟩
    simpa [houtcome, htarget, panOutcomeToPcResult, crepControlToPcResult]
      using hraisedResult

/-! Port the two remaining control-transfer state cases of the declaration
    induction.  Cake's compact result relation fixes the target Break and
    Continue labels to zero; retain that constructor fact and the complete
    evaluator/state premises instead of treating these cases as generic
    forbidden results. -/
theorem PanValuePcSemanticClockEvidence.crossClockBreakOrContinueResultRelWithContextCode_of_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (sourceClock targetClock : Nat)
    (sourceEvidence : PanValuePcSemanticClockEvidence structs context program
      sourceClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (targetEvidence : PanValuePcSemanticClockEvidence structs context program
      targetClock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (inputCodeRel : codeRel context sourceEvidence.sourceInput.code
      targetEvidence.targetInput.code)
    (inputExcpRel : excpRel context sourceEvidence.sourceInput.eshapes
      targetEvidence.targetInput.eshapes)
    (inputStateRel : panValueCrepStateRelWithContext structs context
      sourceEvidence.sourceInput.locals sourceEvidence.sourceInput.globals
      sourceEvidence.sourceInput.memory targetEvidence.targetInput.state)
    (outputCodeRel : codeRel context sourceEvidence.sourceExecution.code
      targetEvidence.targetExecution.code)
    (outputExcpRel : excpRel context sourceEvidence.sourceExecution.eshapes
      targetEvidence.targetExecution.eshapes)
    (hbranch :
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        sourceEvidence.outcome =
          .control (.broke sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        targetEvidence.result = .broke targetState 0) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        sourceEvidence.outcome =
          .control (.continued sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        targetEvidence.result = .continued targetState 0)) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
        globalsLookup (panOutcomeToPcResult sourceEvidence.outcome)
        (crepControlToPcResult targetEvidence.result) ∧
      ∃ sourceLocals sourceGlobals sourceMemory targetState,
        panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
          sourceMemory targetState := by
  have hrel := hcorrect context structs sourceEvidence.sourceInput
    targetEvidence.targetInput exceptionRel sourceEvidence.sourceExecution
    targetEvidence.targetExecution sourceEvidence.sourceInputStructs
    targetEvidence.targetInputStructs sourceEvidence.sourceLocalisedCode
    sourceEvidence.programLocalised inputCodeRel inputExcpRel
    (inputStateRel).2.2 sourceEvidence.sourceNotError sourceEvidence.sourceEval
    targetEvidence.targetEval outputCodeRel outputExcpRel
  rw [sourceEvidence.sourceResult, targetEvidence.targetResult] at hrel
  rcases inputStateRel with ⟨hoverlap, hmax, _⟩
  rcases hbranch with hbreak | hcontinue
  · rcases hbreak with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      targetState, houtcome, hresult⟩
    have hbreakRel :
        panValuePcResultRelWithContextCode structs context exceptionRel
          exceptionCode globalsLookup
          (.broke sourceLocals sourceGlobals sourceMemory) (.broke targetState 0) := by
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hrel
    have hstate := (panValuePcResultRelWithContextCode_broke_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
      sourceMemory targetState).1 hbreakRel
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      ⟨hoverlap, hmax, hstate⟩⟩⟩
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hbreakRel
  · rcases hcontinue with ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi,
      targetState, houtcome, hresult⟩
    have hcontinueRel :
        panValuePcResultRelWithContextCode structs context exceptionRel
          exceptionCode globalsLookup
          (.continued sourceLocals sourceGlobals sourceMemory) (.continued targetState 0) := by
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hrel
    have hstate := (panValuePcResultRelWithContextCode_continued_iff structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
      sourceMemory targetState).1 hcontinueRel
    refine ⟨?_, ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
      ⟨hoverlap, hmax, hstate⟩⟩⟩
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
      using hcontinueRel

theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  have hplain := panValuePcCompileCorrect_of_withContextCode
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup
    program hcorrect
  apply panCrepSemanticAgreement_of_pcResultRel_pair
    structs context exceptionRel exceptionCode globalsLookup panHooks crepHooks
  · intro clock
    let witness := hevidence clock
    refine ⟨witness.outcome, witness.returnedClock, witness.result,
      witness.targetState, witness.panEval, witness.crepEval, ?_, witness.events⟩
    exact PanValuePcSemanticClockEvidence.resultRel hplain clock witness
  · exact hpanSuccess
  · exact hcrepSuccess
  · exact hpanSuccessEvents
  · exact hcrepSuccessEvents

/-! Assemble the same-clock normal/raised dispatcher into the top-level
    semantic agreement.  Unlike the older pairwise adapter, this result also
    returns the strengthened output-state family consumed by the
    `state_rel_imp_semantics_to_crep` induction. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_branch_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputStateRel : ∀ (clock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence clock).sourceInput.locals
        (hevidence clock).sourceInput.globals
        (hevidence clock).sourceInput.memory
        (hevidence clock).targetInput.state)
    (hbranch : ∀ (clock : Nat),
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence clock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence clock).result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence clock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence clock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException))
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks ∧
    ∀ (_clock : Nat), ∃ sourceLocals sourceGlobals sourceMemory targetState,
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_pairwise_evidence
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hcorrect hevidence
      hpanSuccess hcrepSuccess hpanSuccessEvents hcrepSuccessEvents
  refine ⟨hagreement, ?_⟩
  intro _clock
  exact (PanValuePcSemanticClockEvidence.normalOrRaisedResultRelWithContextCode_of_branch
    hcorrect _clock (hevidence _clock) (hinputStateRel _clock) (hbranch _clock)).2

/-! The normal declaration-call branch of `state_rel_imp_semantics_to_crep` is
    useful on its own when the source evaluator has already established that
    every clock terminates normally.  Keep the evaluator, state, result,
    success, and event premises explicit; only the raised alternative is
    discharged by this specialized induction case. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_normal_call_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputStateRel : ∀ (clock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence clock).sourceInput.locals
        (hevidence clock).sourceInput.globals
        (hevidence clock).sourceInput.memory
        (hevidence clock).targetInput.state)
    (hnormal : ∀ (clock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence clock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence clock).result = .normal targetState)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks ∧
    ∀ (_clock : Nat), ∃ sourceLocals sourceGlobals sourceMemory targetState,
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_branch_evidence
    structs context program sourceEvaluate targetEvaluate codeRel excpRel
    exceptionCode globalsLookup exceptionRel panHooks crepHooks hcorrect hevidence
    hinputStateRel (hbranch := by
      intro clock
      left
      exact hnormal clock)
    hpanSuccess hcrepSuccess hpanSuccessEvents hcrepSuccessEvents

/-! Compose pairwise `pc_compile_correct` evidence with the two observational
    prefix chains.  This is the top-level semantic counterpart of Cake's
    `state_rel_imp_semantics_to_crep`; evaluator, state, success, event, and
    chain premises remain explicit. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = [])
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_pairwise_evidence
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hcorrect hevidence
      hpanSuccess hcrepSuccess hpanSuccessEvents hcrepSuccessEvents
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

theorem panCrepSemanticAgreement_of_pcCompileCorrect
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcResultRel_pair structs
    context exceptionRel exceptionCode globalsLookup panHooks crepHooks
  · intro clock
    let witness := hevidence clock
    refine ⟨witness.outcome, witness.returnedClock, witness.result,
      witness.targetState, witness.panEval, witness.crepEval, ?_, witness.events⟩
    have hrel := hcorrect context structs witness.sourceInput
      witness.targetInput exceptionRel witness.sourceExecution
      witness.targetExecution witness.sourceInputStructs
      witness.targetInputStructs witness.sourceLocalisedCode
      witness.programLocalised witness.inputCodeRel witness.inputExcpRel
      witness.stateRel witness.sourceNotError witness.sourceEval
      witness.targetEval witness.outputCodeRel witness.outputExcpRel
    rw [witness.sourceResult, witness.targetResult] at hrel
    exact hrel
  · exact hpanSuccess
  · exact hcrepSuccess
  · exact hpanSuccessEvents
  · exact hcrepSuccessEvents

/-! Compose the plain (non-context-coded) `pc_compile_correct` evidence with
    the observational prefix chains.  This is the plain-result counterpart of
    `panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_pairwise_evidence`;
    keeping both entry points mirrors the two result-relations in the Pancake
    proof and avoids forcing callers to manufacture context-code evidence when
    their proof already establishes the ordinary relation. -/
theorem panCrepBehaviourRel_of_pcCompileCorrect_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = [])
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrect
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hcorrect hevidence
      hpanSuccess hcrepSuccess hpanSuccessEvents hcrepSuccessEvents
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Compose the per-clock `pc_compile_correct` evidence with the genuinely
cross-clock premises from Cake's choice-stability argument. The source and
target evaluator monotonicity is intentionally not inferred from a single
clock's relation: callers must provide `hresultCross` and `heventsCross`. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hresultCross : ∀ (sourceClock targetClock : Nat),
      panValuePcResultRel structs context exceptionRel exceptionCode
        globalsLookup
        (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result))
    (heventsCross : ∀ (sourceClock targetClock : Nat),
      panResultEvents (some ((hevidence sourceClock).outcome,
        (hevidence sourceClock).returnedClock)) =
        crepHooks.ioEvents (hevidence targetClock).targetState) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcResultRel_pair_cross_clock structs context
    exceptionRel exceptionCode globalsLookup panHooks crepHooks hffiOutcome
  · intro clock
    let witness := hevidence clock
    refine ⟨witness.outcome, witness.returnedClock, witness.result,
      witness.targetState, witness.panEval, witness.crepEval, ?_, witness.events⟩
    exact PanValuePcSemanticClockEvidence.resultRel hcorrect clock witness
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    let sourceEvidence := hevidence sourceClock
    let targetEvidence := hevidence targetClock
    have hsourceResult : sourceResult =
        (sourceEvidence.outcome, sourceEvidence.returnedClock) := by
      apply Option.some.inj
      exact hsource.symm.trans sourceEvidence.panEval
    have htargetPair : (targetResult, targetState) =
        (crepControlResultToSemantic (some targetEvidence.result),
          targetEvidence.targetState) :=
      htarget.symm.trans targetEvidence.crepEval
    have htargetResult : targetResult =
        crepControlResultToSemantic (some targetEvidence.result) := by
      exact congrArg Prod.fst htargetPair
    have htargetState : targetState = targetEvidence.targetState :=
      congrArg Prod.snd htargetPair
    refine ⟨sourceEvidence.outcome, sourceEvidence.returnedClock,
      targetEvidence.result, hsourceResult, htargetResult,
      hresultCross sourceClock targetClock, ?_⟩
    simpa [hsourceResult, htargetState] using heventsCross sourceClock targetClock

def panEventPrefix {α : Type} (left right : List α) : Prop :=
  ∃ suffix, right = left ++ suffix

theorem panEventPrefix_antisymm {α : Type} {left right : List α}
    (hleft : panEventPrefix left right)
    (hright : panEventPrefix right left) :
    left = right := by
  rcases hleft with ⟨rightSuffix, hrightEq⟩
  rcases hright with ⟨leftSuffix, hleftEq⟩
  have hleftLen : left.length ≤ right.length := by
    rw [hrightEq, List.length_append]
    omega
  have hrightLen : right.length ≤ left.length := by
    rw [hleftEq, List.length_append]
    omega
  have hlen : left.length = right.length :=
    Nat.le_antisymm hleftLen hrightLen
  have hsuffixLen : rightSuffix.length = 0 := by
    rw [hrightEq, List.length_append] at hlen
    omega
  have hsuffix : rightSuffix = [] :=
    List.eq_nil_iff_length_eq_zero.mpr hsuffixLen
  simp [hrightEq, hsuffix]

/-! Cake supplies monotonicity as mutual event-prefix premises. This wrapper
keeps those premises explicit while reusing the cross-clock compiler bridge. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hresultCross : ∀ (sourceClock targetClock : Nat),
      panValuePcResultRel structs context exceptionRel exceptionCode
        globalsLookup
        (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result))
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))) ) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := hresultCross)
  intro sourceClock targetClock
  exact panEventPrefix_antisymm
    (hsourcePrefix sourceClock targetClock)
    (htargetPrefix sourceClock targetClock)

theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hresultCross : ∀ (sourceClock targetClock : Nat),
      panValuePcResultRel structs context exceptionRel exceptionCode
        globalsLookup
        (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result))
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))) ) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  have hplain := panValuePcCompileCorrect_of_withContextCode
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup
    program hcorrect
  exact panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix
    structs context program sourceEvaluate targetEvaluate codeRel excpRel
    exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hplain
    hevidence hresultCross hsourcePrefix htargetPrefix

/-! Lift the plain cross-clock agreement to the observable behavior relation.
    As in Cake's choice-stability argument, the result relation and both event
    prefixes remain caller-supplied; this theorem only composes them with the
    two prefix-chain semantics. -/
theorem panCrepBehaviourRel_of_pcCompileCorrect_cross_clock_prefix
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hresultCross : ∀ (sourceClock targetClock : Nat),
      panValuePcResultRel structs context exceptionRel exceptionCode
        globalsLookup
        (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result))
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome
      hcorrect hevidence hresultCross hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Derive the plain cross-clock result relation from pairwise evaluator,
    input/output-code, exception-shape, and state evidence.  This is the
    non-context-coded counterpart of the later pairwise adapter; the mutual
    event-prefix premises remain explicit because they carry Cake's
    choice-stability obligation. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix_from_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      exact PanValuePcSemanticClockEvidence.crossResultRel
        hcorrect sourceClock targetClock (hevidence sourceClock)
        (hevidence targetClock) (hinputCodeRel sourceClock targetClock)
        (hinputExcpRel sourceClock targetClock)
        (hstateRel sourceClock targetClock)
        (houtputCodeRel sourceClock targetClock)
        (houtputExcpRel sourceClock targetClock))
    (hsourcePrefix := hsourcePrefix) (htargetPrefix := htargetPrefix)

/-! Complete the plain pairwise adapter through the observable behavior
    relation.  The generated theorem is the direct plain-result analogue of
    the context-coded cross-clock behavior bridge below. -/
theorem panCrepBehaviourRel_of_pcCompileCorrect_cross_clock_prefix_from_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrect sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix_from_pairwise_evidence
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hstateRel houtputCodeRel houtputExcpRel
      hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Compose the normal/raised pairwise result adapter with Cake's top-level
    cross-clock semantic proof.  This is the first top-level evaluator theorem
    that consumes the explicit branch constructors while keeping event-prefix
    choice stability and the FFI outcome law visible. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ clock : Nat,
      PanValuePcSemanticClockEvidence structs context program clock
        sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
        globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hbranch : ∀ (sourceClock targetClock : Nat),
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException))
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      have hpair := panValuePcResultRelWithContextCode_of_pairwise_normalOrRaised_evidence
        hcorrect hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel
        houtputExcpRel hbranch sourceClock targetClock
      exact panValuePcResultRel_of_withContextCode structs context exceptionRel
        exceptionCode globalsLookup _ _ hpair.1)
    (hsourcePrefix := hsourcePrefix) (htargetPrefix := htargetPrefix)

/-! The raised-only top-level declaration branch is the concrete arbitrary
    payload case of Cake's `state_rel_imp_semantics_to_crep` induction.  Keep
    the exception lookup, evaluator/state relations, and both event-prefix
    directions explicit while specializing the normal/raised dispatcher. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_raised_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat),
      PanValuePcSemanticClockEvidence structs context program clock
        sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
        globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hraised : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
    structs context program sourceEvaluate targetEvaluate codeRel excpRel
    exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
    hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel houtputExcpRel
    (hbranch := by
      intro sourceClock targetClock
      right
      exact hraised sourceClock targetClock)
    hsourcePrefix htargetPrefix

/-! The normal-only declaration branch is the value-preserving counterpart of
    the raised adapter above.  Keep the normal evaluator constructors and the
    full context state relation explicit at the semantic boundary. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normal_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat),
      PanValuePcSemanticClockEvidence structs context program clock
        sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
        globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hnormal : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      rcases hnormal sourceClock targetClock with
        ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi, targetState,
          houtcome, hresult⟩
      have hstate := panValueCrepStateRelWithContext_to_stateRel
        structs context (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state
        (hinputStateRel sourceClock targetClock)
      have hplain :=
        PanValuePcSemanticClockEvidence.crossClockNormalResultRel
          hcorrect sourceClock targetClock (hevidence sourceClock)
          (hevidence targetClock) (hinputCodeRel sourceClock targetClock)
          (hinputExcpRel sourceClock targetClock) hstate
          (houtputCodeRel sourceClock targetClock)
          (houtputExcpRel sourceClock targetClock)
          sourceLocals sourceGlobals sourceMemory sourceFfi targetState
          houtcome hresult
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hplain)
    (hsourcePrefix := hsourcePrefix) (htargetPrefix := htargetPrefix)

/-! Lift the normal-only declaration adapter to observable behavior.
    The normal branch, state-context relation, and both event-prefix chains
    remain explicit at this boundary. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normal_stateRelWithContext
    {α σ : Type}
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat),
      PanValuePcSemanticClockEvidence structs context program clock
        sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
        globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hnormal : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normal_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel
      houtputExcpRel hnormal hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Expose the branch-explicit clocked evaluator bridge at the behavior level.
    This is the declaration-induction shape of `state_rel_imp_semantics_to_crep`:
    the normal/raised witness, full context state relation, evaluator evidence,
    and both cross-clock event prefixes remain caller-supplied. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hbranch : ∀ (sourceClock targetClock : Nat),
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi targetState,
        (hevidence sourceClock).outcome =
          .control (.normal sourceLocals sourceGlobals sourceMemory sourceFfi) ∧
        (hevidence targetClock).result = .normal targetState) ∨
      (∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException))
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel houtputExcpRel
      hbranch hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Lift the raised-only clocked branch all the way to the behavior relation.
    This is the usable top-level arbitrary-payload case: the source/target
    state package, exception lookup, evaluator equations, and both prefix
    chains remain explicit rather than being hidden in a semantic alias. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_raised_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hraised : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceException
          sourceValue targetState targetException,
        (hevidence sourceClock).outcome =
          .control (.raised sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceException sourceValue) ∧
        (hevidence targetClock).result = .raised targetState targetException ∧
        lookupInfo sourceException context.exceptions = some targetException)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_raised_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel houtputExcpRel
      hraised hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! The returned branch of the same declaration induction carries an explicit
    value list, but its state transport is still obtained from the strengthened
    context relation.  The result relation is obtained from the explicit
    cross-clock `pc_compile_correct` premises. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_returned_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hreturned : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceValues targetState targetValues,
        (hevidence sourceClock).outcome =
          .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi sourceValues) ∧
        (hevidence targetClock).result = .returned targetState targetValues)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks ∧
    ∀ (_clock : Nat), ∃ sourceLocals sourceGlobals sourceMemory targetState,
      panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  have hresultCross : ∀ (sourceClock targetClock : Nat),
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult (hevidence sourceClock).outcome)
        (crepControlToPcResult (hevidence targetClock).result) := by
    intro sourceClock targetClock
    exact PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
      hcorrect sourceClock targetClock (hevidence sourceClock) (hevidence targetClock)
      (hinputCodeRel sourceClock targetClock) (hinputExcpRel sourceClock targetClock)
      (hinputStateRel sourceClock targetClock).2.2
      (houtputCodeRel sourceClock targetClock) (houtputExcpRel sourceClock targetClock)
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hresultCross hsourcePrefix htargetPrefix
  refine ⟨hagreement, ?_⟩
  intro clock
  rcases hreturned clock clock with ⟨sourceLocals, sourceGlobals, sourceMemory,
    _sourceFfi, sourceValues, targetState, targetValues, houtcome, hresult⟩
  rcases hinputStateRel clock clock with ⟨hoverlap, hmax, _hstate⟩
  have hrel := PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
    hcorrect clock clock (hevidence clock) (hevidence clock)
    (hinputCodeRel clock clock) (hinputExcpRel clock clock)
    (hinputStateRel clock clock).2.2 (houtputCodeRel clock clock)
    (houtputExcpRel clock clock)
  have hreturnedRel :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
        (.returned targetState targetValues) := by
    simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult] using hrel
  have hstate := (panValuePcResultRel_returned_iff structs context exceptionRel
    exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory sourceValues
    targetState targetValues).1 hreturnedRel
  exact ⟨sourceLocals, sourceGlobals, sourceMemory, targetState,
    ⟨hoverlap, hmax, hstate.1⟩⟩

/-! Lift the returned-result state bridge through Cake's clock-indexed
    observational wrappers.  The evaluator, state, returned-value, and
    bidirectional event-prefix premises stay explicit at this boundary. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_returned_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hreturned : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceValues targetState targetValues,
        (hevidence sourceClock).outcome =
          .control (.returned sourceLocals sourceGlobals sourceMemory sourceFfi sourceValues) ∧
        (hevidence targetClock).result = .returned targetState targetValues)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_returned_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome
      hcorrect hevidence hinputCodeRel hinputExcpRel hinputStateRel houtputCodeRel
      houtputExcpRel hreturned hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement.1 panChain crepChain

/-! Derive the cross-clock context-coded result relation from the two clock
    witnesses themselves.  The input/output code and exception relations and
    the state relation remain explicit for each clock pair; only the
    context-code projection and the final semantic-agreement composition are
    discharged here. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))) ) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      exact PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
        hcorrect sourceClock targetClock (hevidence sourceClock)
        (hevidence targetClock) (hinputCodeRel sourceClock targetClock)
        (hinputExcpRel sourceClock targetClock)
        (hstateRel sourceClock targetClock)
        (houtputCodeRel sourceClock targetClock)
        (houtputExcpRel sourceClock targetClock))
    (hsourcePrefix := hsourcePrefix) (htargetPrefix := htargetPrefix)

/-! Use the full Cake `state_rel` package at the top-level cross-clock
    boundary.  The evaluator, code, exception, and two event-prefix premises
    remain explicit; this adapter only projects the state relation's ordinary
    component for the result-relation induction. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence
    structs context program sourceEvaluate targetEvaluate codeRel excpRel
    exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
    hevidence hinputCodeRel hinputExcpRel
    (hstateRel := fun sourceClock targetClock =>
      panValueCrepStateRelWithContext_to_stateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state
        (hstateRel sourceClock targetClock))
    houtputCodeRel houtputExcpRel hsourcePrefix htargetPrefix


/-! The terminal-FFI-only declaration branch packages the existing
    cross-clock FinalFFI relation with the full Cake context state relation.
    FinalFFI remains a distinct successful observation, with its event
    preserved by the context-coded result relation rather than being treated
    as a returned value. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_finalFfi_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hfinalFfi : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceEvent targetState
          targetEvent,
        (hevidence sourceClock).outcome =
          .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceEvent) ∧
        (hevidence targetClock).result = .finalFfi targetState targetEvent)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  apply panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hcorrect) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      rcases hfinalFfi sourceClock targetClock with
        ⟨sourceLocals, sourceGlobals, sourceMemory, sourceFfi, sourceEvent,
          targetState, targetEvent, houtcome, hresult⟩
      have hstate := panValueCrepStateRelWithContext_to_stateRel
        structs context (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state
        (hstateRel sourceClock targetClock)
      have hplain :=
        PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRel
          hcorrect sourceClock targetClock (hevidence sourceClock)
          (hevidence targetClock) (hinputCodeRel sourceClock targetClock)
          (hinputExcpRel sourceClock targetClock) hstate
          (houtputCodeRel sourceClock targetClock)
          (houtputExcpRel sourceClock targetClock)
          sourceLocals sourceGlobals sourceMemory sourceFfi sourceEvent
          targetState targetEvent houtcome hresult
      have hparts := (panValuePcResultRel_finalFfi_iff structs context
        exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
        sourceMemory sourceEvent targetState targetEvent).1 hplain
      have hcontext := (panValuePcResultRelWithContextCode_finalFfi_iff
        structs context exceptionRel exceptionCode globalsLookup sourceLocals
        sourceGlobals sourceMemory sourceEvent targetState targetEvent).2 hparts
      have hresultRel := panValuePcResultRel_of_withContextCode
        structs context exceptionRel exceptionCode globalsLookup _ _ hcontext
      simpa [houtcome, hresult, panOutcomeToPcResult, crepControlToPcResult]
        using hresultRel)
    (hsourcePrefix := hsourcePrefix) (htargetPrefix := htargetPrefix)


/-! Behavior-level FinalFFI wrapper for the preceding state-context adapter.
    The source and target prefix chains remain explicit, so the observable
    behavior theorem preserves the same event and FinalFFI branch premises. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_finalFfi_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hfinalFfi : ∀ (sourceClock targetClock : Nat),
      ∃ sourceLocals sourceGlobals sourceMemory sourceFfi sourceEvent targetState
          targetEvent,
        (hevidence sourceClock).outcome =
          .control (.finalFfi sourceLocals sourceGlobals sourceMemory sourceFfi
            sourceEvent) ∧
        (hevidence targetClock).result = .finalFfi targetState targetEvent)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_finalFfi_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome
      hcorrect hevidence hinputCodeRel hinputExcpRel hstateRel houtputCodeRel
      houtputExcpRel hfinalFfi hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Behavior-level wrapper for the full Cake state relation.  This keeps the
    bundled context invariants at the caller boundary while exposing the final
    observable behavior relation directly. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs context
      program clock sourceEvaluate targetEvaluate codeRel excpRel exceptionRel
      exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hstateRel houtputCodeRel houtputExcpRel
      hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Complete the production clock-family induction with Cake's bundled state
    relation.  The pairwise evaluator correctness premise remains explicit;
    the result relation therefore retains every `pc_compile_correct` result
    constructor, while the two prefix directions retain the source
    prefix-LUB obligation instead of assuming event equality. -/
theorem panCrepBehaviourRel_of_clocked_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext
    [BEq α] [OfNat α 0] [Add α] [BEq String]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : Nat → PanValuePcEvaluator α)
    (targetEvaluate : Nat → CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : ∀ (sourceClock targetClock : Nat),
      PanValuePcCompileCorrectWithContextCode
        (sourceEvaluate sourceClock) (targetEvaluate targetClock)
        codeRel excpRel exceptionCode globalsLookup program)
    (evidence : ∀ (clock : Nat),
      PanValuePcSemanticClockEvidence structs context program clock
        (sourceEvaluate clock) (targetEvaluate clock) codeRel excpRel
        exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (evidence sourceClock).sourceInput.code
        (evidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (evidence sourceClock).sourceInput.eshapes
        (evidence targetClock).targetInput.eshapes)
    (hinputStateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRelWithContext structs context
        (evidence sourceClock).sourceInput.locals
        (evidence sourceClock).sourceInput.globals
        (evidence sourceClock).sourceInput.memory
        (evidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (evidence sourceClock).sourceExecution.code
        (evidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (evidence sourceClock).sourceExecution.eshapes
        (evidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((evidence sourceClock).outcome,
          (evidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (evidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (evidence targetClock).targetState)
        (panResultEvents (some ((evidence sourceClock).outcome,
          (evidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_clocked_pcCompileCorrectWithContextCode
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome
      hcorrect evidence evidence hinputCodeRel hinputExcpRel
      (fun sourceClock targetClock =>
        (hinputStateRel sourceClock targetClock).2.2)
      houtputCodeRel houtputExcpRel (by
        intro sourceClock targetClock
        exact panEventPrefix_antisymm
          (hsourcePrefix sourceClock targetClock)
          (htargetPrefix sourceClock targetClock))
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! Cross-clock counterpart of the behavior adapter.  The source and target
    prefix witnesses are kept explicit so this reaches the Cake semantic
    behavior result without hiding the monotonicity obligation. -/
theorem panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (hsourcePrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock)))
        (crepHooks.ioEvents (hevidence targetClock).targetState))
    (htargetPrefix : ∀ (sourceClock targetClock : Nat),
      panEventPrefix
        (crepHooks.ioEvents (hevidence targetClock).targetState)
        (panResultEvents (some ((hevidence sourceClock).outcome,
          (hevidence sourceClock).returnedClock))))
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hagreement :=
    panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence
      structs context program sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup exceptionRel panHooks crepHooks hffiOutcome hcorrect
      hevidence hinputCodeRel hinputExcpRel hstateRel houtputCodeRel houtputExcpRel
      hsourcePrefix htargetPrefix
  exact panSemantics_rel_crepSemantics panHooks crepHooks hagreement panChain crepChain

/-! The same pairwise evidence adapter without the prefix packaging.  This is
    the direct choice-stability boundary: evaluator/code/state relations
    discharge the cross-clock result relation, while exact cross-clock event
    equality remains an explicit Cake monotonicity premise. -/
theorem panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_from_pairwise_evidence
    [BEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α) (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks α)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (hevidence : ∀ (clock : Nat), PanValuePcSemanticClockEvidence structs
      context program clock sourceEvaluate targetEvaluate codeRel excpRel
      exceptionRel exceptionCode globalsLookup panHooks crepHooks)
    (hinputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceInput.code
        (hevidence targetClock).targetInput.code)
    (hinputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceInput.eshapes
        (hevidence targetClock).targetInput.eshapes)
    (hstateRel : ∀ (sourceClock targetClock : Nat),
      panValueCrepStateRel structs context
        (hevidence sourceClock).sourceInput.locals
        (hevidence sourceClock).sourceInput.globals
        (hevidence sourceClock).sourceInput.memory
        (hevidence targetClock).targetInput.state)
    (houtputCodeRel : ∀ (sourceClock targetClock : Nat),
      codeRel context (hevidence sourceClock).sourceExecution.code
        (hevidence targetClock).targetExecution.code)
    (houtputExcpRel : ∀ (sourceClock targetClock : Nat),
      excpRel context (hevidence sourceClock).sourceExecution.eshapes
        (hevidence targetClock).targetExecution.eshapes)
    (heventsCross : ∀ (sourceClock targetClock : Nat),
      panResultEvents (some ((hevidence sourceClock).outcome,
        (hevidence sourceClock).returnedClock)) =
        crepHooks.ioEvents (hevidence targetClock).targetState) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  have hplain := panValuePcCompileCorrect_of_withContextCode
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup
    program hcorrect
  apply panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock
    (structs := structs) (context := context) (program := program)
    (sourceEvaluate := sourceEvaluate) (targetEvaluate := targetEvaluate)
    (codeRel := codeRel) (excpRel := excpRel)
    (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
    (exceptionRel := exceptionRel) (panHooks := panHooks)
    (crepHooks := crepHooks) (hffiOutcome := hffiOutcome)
    (hcorrect := hplain) (hevidence := hevidence)
    (hresultCross := by
      intro sourceClock targetClock
      exact PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
        hcorrect sourceClock targetClock (hevidence sourceClock)
        (hevidence targetClock) (hinputCodeRel sourceClock targetClock)
        (hinputExcpRel sourceClock targetClock)
        (hstateRel sourceClock targetClock)
        (houtputCodeRel sourceClock targetClock)
        (houtputExcpRel sourceClock targetClock))
    (heventsCross := heventsCross)

/-! ## A concrete no-final-FFI instantiation

This instantiation has a normal run at clock `0` and a successful returned run at
every positive clock, so the outcome and event fields of
`PanCrepSemanticAgreement` are exercised against a genuine `panValueCrepStateRel`
rather than the vacuous no-run hooks of `Flapjack/Test/PanToCrepSemantics.lean`. -/

def demoFfiState : FfiState Unit where
  oracle := fun _ _ _ _ => .final .failed
  state := ()
  ioEvents := []

def demoPanHooks : PanSemanticsHooks Nat Unit where
  evaluate := fun clock =>
    if clock = 0 then
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        demoFfiState), 0)
    else
      some (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        demoFfiState [PanValue.word 41]), clock)
  ffiOutcome := fun event => event.outcome

def demoCrepState : CrepState Nat where
  locals := fun _ => none
  memory := fun _ => none
  globals := fun _ => none

def demoCrepHooks : CrepSemanticsHooks Nat where
  evaluate := fun clock =>
    if clock = 0 then
      (crepControlResultToSemantic (some (.normal demoCrepState)), demoCrepState)
    else
      (crepControlResultToSemantic (some (.returned demoCrepState [41])),
        demoCrepState)
  ioEvents := fun _ => []

def demoContext : CompileContext Nat where
  vars := []
  functions := []
  exceptions := []
  maxVar := 0
  bytesInWord := 8

theorem demoPanValueCrepStateRel :
    panValueCrepStateRel [] demoContext (fun _ => none) (fun _ => none)
      (fun _ => none) demoCrepState := by
  refine ⟨rfl, ?_, rfl⟩
  intro name value shape slots hsource _
  simp at hsource

set_option linter.unusedSimpArgs false in
theorem demoPanCrepSemanticAgreement :
    PanCrepSemanticAgreement demoPanHooks demoCrepHooks := by
  apply panCrepSemanticAgreement_of_pcResultRel_pair [] demoContext
    (fun _ _ _ => True) (fun _ => none) (fun _ _ => none) demoPanHooks demoCrepHooks
  · intro clock
    by_cases hclock : clock = 0
    · subst hclock
      exact ⟨.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
          demoFfiState), 0, .normal demoCrepState, demoCrepState,
        by simp [demoPanHooks],
        by simp [demoCrepHooks],
        demoPanValueCrepStateRel,
        by simp [demoPanHooks, demoCrepHooks, demoFfiState, panResultEvents,
          panResultFfi]⟩
    · exact ⟨.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
          demoFfiState [PanValue.word 41]), clock, .returned demoCrepState [41],
        demoCrepState,
        by simp [demoPanHooks, hclock],
        by simp [demoCrepHooks, hclock],
        ⟨demoPanValueCrepStateRel,
          by simp [panValueCrepValuesRel, panValueFlatWords, panValueFlatWordsFuel, panValueFlatValueFuel]⟩,
        by simp [demoPanHooks, demoCrepHooks, demoFfiState, hclock,
          panResultEvents, panResultFfi]⟩
  · intro clock sourceResult sourceOutcome hsource houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have hsrc : sourceResult =
          (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState), 0) := by simpa [demoPanHooks] using hsource.symm
      rw [hsrc] at houtcome
      simp only [panResultOutcome] at houtcome
      simp at houtcome
    · have hsrc : sourceResult =
          (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState [PanValue.word 41]), clock) := by
        simpa [demoPanHooks, hclock] using hsource.symm
      rw [hsrc] at houtcome
      simp only [panResultOutcome] at houtcome
      simpa using houtcome.symm
  · intro clock targetResult targetState targetOutcome htarget houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have htgt : targetResult =
          crepControlResultToSemantic (some (.normal demoCrepState)) := by
        simpa [demoCrepHooks] using (congrArg Prod.fst htarget).symm
      rw [htgt] at houtcome
      simp only [crepControlResultToSemantic, crepResultOutcome] at houtcome
      simp at houtcome
    · have htgt : targetResult =
          crepControlResultToSemantic (some (.returned demoCrepState [41])) := by
        simpa [demoCrepHooks, hclock] using (congrArg Prod.fst htarget).symm
      rw [htgt] at houtcome
      simp only [crepControlResultToSemantic, crepResultOutcome] at houtcome
      simpa using houtcome.symm
  · intro clock sourceResult sourceOutcome hsource _houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have hsrc : sourceResult =
          (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState), 0) := by simpa [demoPanHooks] using hsource.symm
      rw [hsrc]
      simp [panResultEvents, panResultFfi, demoFfiState, demoCrepHooks]
    · have hsrc : sourceResult =
          (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState [PanValue.word 41]), clock) := by
        simpa [demoPanHooks, hclock] using hsource.symm
      rw [hsrc]
      simp [panResultEvents, panResultFfi, demoFfiState, demoCrepHooks]
  · intro clock targetResult targetState targetOutcome _htarget _houtcome
    by_cases hclock : clock = 0
    · subst hclock
      simp [demoCrepHooks]
    · simp [demoCrepHooks, hclock]

end Flapjack
