import Flapjack.CrepeProgramInduction
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramIteCorrectness
import Flapjack.CrepeProgramWhileCorrectness

/-!
The checked Lean boundary corresponding to CakeML's
`pan_to_crepProofScript.sml` theorem `pc_compile_correct` (line 442).

The compact `PanValueControlResult` evaluator predates the clocked/FFI
boundary and therefore cannot express `TimeOut` or `FinalFFI`.  This module
keeps the existing source-to-Crep state, global, memory, exception, and
flattened-value relations, while adding those two result cases explicitly.
The evaluator obligations are parameters: the theorem below is the
kernel-checked assembly boundary to be discharged by the source and Crep
semantic proofs for each supported compiler subset.  The current
`panValueCrepStateRel` is deliberately a supported-empty-global relation
(`sourceGlobals = fun _ => none`); the code and exception-shape relations,
`globalsLookup`, and the localised-program premise remain explicit parameters
until global lowering is completed.
-/

namespace Flapjack

/-! Source-side result cases from HOL `pc_compile_correct`, including the
`Error` case excluded by that theorem's premise. -/
inductive PanValuePcResult (α : Type u) where
  | error
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | finalFfi (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (event : FfiFinalEvent)

/-! Crep-side result cases are the corresponding target observations.  The
target `error` constructor is retained so the boundary can state the HOL
non-error premise symmetrically, even though the current full Crep evaluator
reports failures through `none`. -/
inductive CrepPcResult (α : Type u) where
  | error
  | normal (state : CrepState α)
  | returned (state : CrepState α) (values : List α)
  | raised (state : CrepState α) (exception : α)
  | broke (state : CrepState α) (label : Nat)
  | continued (state : CrepState α) (label : Nat)
  | timeout (state : CrepState α)
  | finalFfi (state : CrepState α) (event : FfiFinalEvent)

abbrev PanValuePcSourceCode α :=
  List (FunName × List VarName × Prog α)

abbrev PanValuePcTargetCode α :=
  List (CompiledFunction α)

abbrev PanValuePcCodeRel α :=
  CompileContext α → PanValuePcSourceCode α → PanValuePcTargetCode α → Prop

abbrev PanValuePcExceptionShapeRel α :=
  CompileContext α → InfoMap Shape → InfoMap Shape → Prop

def panValuePcLocalisedCode (code : PanValuePcSourceCode α) : Prop :=
  ∀ entry ∈ code, localisedProg entry.2.2

/-! The exception clause of HOL `pc_compile_correct`: the target exception is
the code looked up for the source exception, and a non-empty payload is
available through `globalsLookup` with the same flattening and 32-word bound.
The lookup functions are parameters because the current Lean state relation
still models only the empty source-global boundary. -/
def panValuePcExceptionResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α) : Prop :=
  ∃ spillAddress code,
    exceptionCode sourceException = some code ∧
    targetException = code ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException spillAddress ∧
    (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue) ∧
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)

/-! Exact Cake exception-code provenance for the raised result clause.  The
    compatibility relation above keeps the historical result-code adapter
    usable, but Cake's `pc_compile_correct` does not permit an unrelated code
    map: its target code is `FLOOKUP ctxt.eids eid`.  This strengthened
    relation makes that missing premise explicit at the boundary. -/
def panValuePcExceptionResultRelWithContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α) : Prop :=
  panValuePcExceptionResultRel structs context exceptionRel exceptionCode
    globalsLookup sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException ∧
  lookupInfo sourceException context.exceptions = some targetException

/-! The explicit state/global/memory result relation.  The raised branch uses
the compiler-owned spill relation already used by the downstream Crep
correctness lemmas; timeout and FinalFFI retain the ordinary state relation. -/
def panValuePcResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    : PanValuePcResult α → CrepPcResult α → Prop
  | .error, _ => False
  | .normal sourceLocals sourceGlobals sourceMemory,
      .normal targetState =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .returned sourceLocals sourceGlobals sourceMemory sourceValues,
      .returned targetState targetValues =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValueCrepValuesRel sourceValues targetValues
  | .raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue,
      .raised targetState targetException =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException
  | .broke sourceLocals sourceGlobals sourceMemory, .broke targetState 0 =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .continued sourceLocals sourceGlobals sourceMemory, .continued targetState 0 =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .timeout sourceLocals sourceGlobals sourceMemory, .timeout targetState =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent,
      .finalFfi targetState targetEvent =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧ sourceEvent = targetEvent
  | _, _ => False

def panValuePcResultRelWithContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α)) :
    PanValuePcResult α → CrepPcResult α → Prop
  | .raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue,
      .raised targetState targetException =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException
  | sourceResult, targetResult =>
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceResult targetResult

/-! The source compiler-correctness theorem only permits the loop-control
label `0` at this boundary.  Keep these rejection lemmas next to the
relation so a future broadening of the pattern cannot silently weaken the
statement back to an arbitrary target label. -/
theorem panValuePcResultRel_broke_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.broke sourceLocals sourceGlobals sourceMemory)
      (.broke targetState label) := by
  simp [panValuePcResultRel, hlabel]

theorem panValuePcResultRel_continued_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.continued sourceLocals sourceGlobals sourceMemory)
      (.continued targetState label) := by
  simp [panValuePcResultRel, hlabel]

/-! Safety obligation for the compact `pc_compile_correct` bridge.  The
intermediate control relation intentionally permits nonzero labels while a
loop propagates them, but the final Pancake theorem only admits label `0` for
the result exposed at its boundary. -/
def panValuePcControlLabelSafe
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α) : Prop :=
  match sourceResult, crepResult with
  | .broke _ _ _, .broke _ label => label = 0
  | .continued _ _ _, .continued _ label => label = 0
  | _, _ => True

def PanValueCrepProgramStateControlSafe
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (_exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory program = some sourceResult →
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context program) = some crepResult →
    panValuePcControlLabelSafe sourceResult crepResult

/-! The two primitive loop-control constructors already produce label `0` in
the source and stateful Crep evaluators.  These leaf proofs discharge the
first concrete instances of the safety premise required by the Pc bridge. -/
theorem panValueCrepProgramStateControlSafe_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.break : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          cases hcrep
          rfl

theorem panValueCrepProgramStateControlSafe_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.continue : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          cases hcrep
          rfl

theorem panValueCrepProgramStateControlSafe_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : Exp α) :
    PanValueCrepProgramStateControlSafe (.raise exception expression) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some value =>
          cases hvalid : panValuePayloadWithinLimit structs value with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                at hsource
          | true =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                at hsource
              cases hsource
              simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_seq
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (first second : Prog α)
    (hfirstCorrect : PanValueCrepProgramStateCorrect first)
    (hfirstSafe : PanValueCrepProgramStateControlSafe first)
    (hsecondSafe : PanValueCrepProgramStateControlSafe second) :
    PanValueCrepProgramStateControlSafe (.seq first second) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hcompile :
      compileProg context (.seq first second) =
        .seq (compileProg context first) (compileProg context second) := by
    simp [compileProg]
  rw [hcompile] at hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hfirstSource : evalPanValueProgWithPrimitiveCallsAndFfi
              primitive sourceHandler structs sourceFunctions
              baseAddress topAddress bytesInWord sourceFuel
              sourceLocals sourceGlobals sourceMemory first with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                hfirstSource] at hsource
          | some firstSourceResult =>
              cases hfirstCrep : evalCrepFullProgState functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state (compileProg context first) with
              | none =>
                  simp [evalCrepFullProgState, hfirstCrep] at hcrep
              | some firstCrepResult =>
                  have hfirstSafeResult := hfirstSafe context structs sourceFunctions functions
                    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                    sourceFuel targetFuel exceptionRel firstSourceResult firstCrepResult
                    hrel hfirstSource hfirstCrep
                  have hfirstRel := hfirstCorrect context structs sourceFunctions functions
                    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                    sourceFuel targetFuel exceptionRel firstSourceResult firstCrepResult
                    hrel hfirstSource hfirstCrep
                  cases firstSourceResult with
                  | normal firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState =>
                          have hstateRel :
                              panValueCrepStateRel structs context firstLocals firstGlobals
                                firstMemory firstState := by
                            simpa [panValueCrepControlRel] using hfirstRel
                          have hsourceSecond :
                              evalPanValueProgWithPrimitiveCallsAndFfi
                                primitive sourceHandler structs sourceFunctions
                                baseAddress topAddress bytesInWord sourceFuel
                                firstLocals firstGlobals firstMemory second =
                              some sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepSecond :
                              evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                baseAddress topAddress targetFuel firstState
                                (compileProg context second) = some crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          exact hsecondSafe context structs sourceFunctions functions
                            firstLocals firstGlobals firstMemory firstState primitive
                            sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord sourceFuel targetFuel exceptionRel sourceResult
                            crepResult hstateRel hsourceSecond hcrepSecond
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | returned firstLocals firstGlobals firstMemory values =>
                      cases firstCrepResult with
                      | normal firstState
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | returned firstState firstValues =>
                          have hsourceEq :
                              PanValueControlResult.returned firstLocals firstGlobals
                                  firstMemory values = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.returned firstState firstValues = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | raised firstLocals firstGlobals firstMemory exception value =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | raised firstState exceptionCode =>
                          have hsourceEq :
                              PanValueControlResult.raised firstLocals firstGlobals
                                  firstMemory exception value = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.raised firstState exceptionCode = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | broke firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | raised firstState exception
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | broke firstState label =>
                          have hsourceEq :
                              PanValueControlResult.broke firstLocals firstGlobals
                                  firstMemory = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.broke firstState label = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | continued firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | continued firstState label =>
                          have hsourceEq :
                              PanValueControlResult.continued firstLocals firstGlobals
                                  firstMemory = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.continued firstState label = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult

theorem panValueCrepProgramStateControlSafe_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe
      (.ite condition.toExp thenBranch elseBranch) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord condition.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource
          | some conditionValue =>
              cases conditionValue with
              | word sourceCondition =>
                  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory state.locals state.memory
                      baseAddress topAddress bytesInWord
                      (hbytesInWord context bytesInWord)
                      hrel.2.1 (hlookup context sourceLocals) condition
                      sourceCondition hcondition
                  have hcompile : compileProg context
                      (.ite condition.toExp thenBranch elseBranch) =
                      .ite compiledCondition (compileProg context thenBranch)
                        (compileProg context elseBranch) := by
                    simp [compileProg, hcompileCondition]
                  have hcrepConditionState :
                      evalCrepFullExpState state baseAddress topAddress
                        compiledCondition = some sourceCondition := by
                    obtain ⟨compiledCondition', hcompileCondition', hnoGlobal⟩ :=
                      compileSourceWordExp_noGlobal context structs sourceLocals
                        sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                        (hlookup context sourceLocals) condition sourceCondition
                        hcondition
                    have hcompiledEq : compiledCondition = compiledCondition' := by
                      have hpair : ([compiledCondition], Shape.one) =
                          ([compiledCondition'], Shape.one) :=
                        hcompileCondition.symm.trans hcompileCondition'
                      exact (List.cons.inj (congrArg Prod.fst hpair)).1
                    have hcrepCondition' :
                        evalCrepFullExp state.locals state.memory
                          baseAddress topAddress compiledCondition' =
                          some sourceCondition := by
                      simpa [hcompiledEq] using hcrepCondition
                    rw [hcompiledEq]
                    rw [evalCrepFullExpState_eq_of_noGlobal state
                      baseAddress topAddress compiledCondition' hnoGlobal]
                    exact hcrepCondition'
                  rw [hcompile] at hcrep
                  by_cases hnonzero : sourceCondition ≠ 0
                  · have hsourceThen :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory thenBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepThen :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context thenBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    exact hthenSafe context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceThen hcrepThen
                  · have hzero : sourceCondition = 0 := by
                      exact Classical.byContradiction (fun hnot => hnonzero hnot)
                    have hsourceElse :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory elseBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepElse :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context elseBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    exact helseSafe context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceElse hcrepElse
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource

/-! A conditional source program needs both halves of the `pc_compile_correct`
    obligation: the stateful evaluator simulation and the final label-zero
    control safety rule.  Keep them paired so a future conditional proof
    cannot discharge only the control observation while omitting execution
    correctness. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthenCorrect : PanValueCrepProgramStateCorrect thenBranch)
    (helseCorrect : PanValueCrepProgramStateCorrect elseBranch)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.ite condition.toExp thenBranch elseBranch) ∧
      PanValueCrepProgramStateControlSafe
        (.ite condition.toExp thenBranch elseBranch) := by
  constructor
  · exact panValueCrepProgramStateCorrect_ite_source_word condition
      thenBranch elseBranch hthenCorrect helseCorrect hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_ite_source_word condition
      thenBranch elseBranch hthenSafe helseSafe hbytesInWord hlookup

theorem panValueCrepProgramStateControlSafe_while_of_loop_safe
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body)) :
    PanValueCrepProgramStateControlSafe
      (.while condition.toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hrel hsource hcrep
  exact hloopSafe context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel sourceResult crepResult
    hrel hsource hcrep

/-! Pair the stateful while simulation with its final Pc control-safety
    obligation.  The body needs the loop-aware safety relation used by the
    evaluator induction, while the complete while program separately needs
    the boundary label-zero relation. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_while_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.while condition.toExp body) ∧
      PanValueCrepProgramStateControlSafe
        (.while condition.toExp body) := by
  constructor
  · exact panValueCrepProgramStateCorrect_while_source_word condition body
      hbody hbodySafe hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_while_of_loop_safe condition
      body hloopSafe

theorem panValueCrepProgramLoopStateControlSafe_while_zero
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (body : Prog α) :
    PanValueCrepProgramLoopStateControlSafe
      (.while (SourceWordExp.const (0 : α)).toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            SourceWordExp.toExp, evalPanValueExp,
            evalCrepFullProgState, evalCrepFullExpState, compileProg,
            compileExp] at hsource hcrep
          cases hsource
          cases hcrep
          simp

structure PanValuePcInput (α : Type u) where
  structs : StructContext
  code : PanValuePcSourceCode α
  eshapes : InfoMap Shape
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)

structure CrepPcInput (α : Type u) where
  structs : StructContext
  code : PanValuePcTargetCode α
  eshapes : InfoMap Shape
  state : CrepState α

structure PanValuePcExecution (α : Type u) where
  code : PanValuePcSourceCode α
  eshapes : InfoMap Shape
  result : PanValuePcResult α

structure CrepPcExecution (α : Type u) where
  code : PanValuePcTargetCode α
  eshapes : InfoMap Shape
  result : CrepPcResult α

abbrev PanValuePcEvaluator (α : Type u) :=
  CompileContext α → PanValuePcInput α → Prog α → Option (PanValuePcExecution α)

abbrev CrepPcEvaluator (α : Type u) :=
  CompileContext α → CrepPcInput α → CrepProg α → Option (CrepPcExecution α)

/-! The direct Lean analogue of the quantifier/implication shape of HOL
`pc_compile_correct`: code/exceptions/localisation assumptions, related
initial source/target state, successful non-error source and compiled-target
evaluations, then the complete result relation. -/
def PanValuePcCompileCorrect
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceExecution : PanValuePcExecution α)
    (targetExecution : CrepPcExecution α),
    sourceInput.structs = structs →
    targetInput.structs = structs →
    panValuePcLocalisedCode sourceInput.code →
    localisedProg program →
    codeRel context sourceInput.code targetInput.code →
    excpRel context sourceInput.eshapes targetInput.eshapes →
    panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state →
    sourceExecution.result ≠ .error →
    sourceEvaluate context sourceInput program = some sourceExecution →
    targetEvaluate context targetInput (compileProg context program) =
      some targetExecution →
    codeRel context sourceExecution.code targetExecution.code →
    excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceExecution.result targetExecution.result

def PanValuePcCompileCorrectWithContextCode
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceExecution : PanValuePcExecution α)
    (targetExecution : CrepPcExecution α),
    sourceInput.structs = structs →
    targetInput.structs = structs →
    panValuePcLocalisedCode sourceInput.code →
    localisedProg program →
    codeRel context sourceInput.code targetInput.code →
    excpRel context sourceInput.eshapes targetInput.eshapes →
    panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state →
    sourceExecution.result ≠ .error →
    sourceEvaluate context sourceInput program = some sourceExecution →
    targetEvaluate context targetInput (compileProg context program) =
      some targetExecution →
    codeRel context sourceExecution.code targetExecution.code →
    excpRel context sourceExecution.eshapes targetExecution.eshapes →
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup sourceExecution.result targetExecution.result

/-! Packaging theorem for a supported compiler subset.  Every HOL result case
is an explicit obligation; in particular no proof can discharge this
boundary by silently dropping timeout or FinalFFI. -/
theorem panValuePcCompileCorrect_of_obligations
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (hobligation : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceExecution : PanValuePcExecution α)
      (targetExecution : CrepPcExecution α),
      sourceInput.structs = structs →
      targetInput.structs = structs →
      panValuePcLocalisedCode sourceInput.code →
      localisedProg program →
      codeRel context sourceInput.code targetInput.code →
      excpRel context sourceInput.eshapes targetInput.eshapes →
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetInput.state →
      sourceExecution.result ≠ .error →
      sourceEvaluate context sourceInput program = some sourceExecution →
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      codeRel context sourceExecution.code targetExecution.code →
      excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hlocalisedCode hlocalised hcode hexcp hstate
    hnonerror hsource htarget hpostCode hpostExcp
  exact hobligation context structs sourceInput targetInput exceptionRel
    sourceExecution targetExecution hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp

end Flapjack
