import Flapjack.CrepeProgramInduction

/-!
The checked Lean boundary corresponding to CakeML's
`pan_to_crepProofScript.sml` theorem `pc_compile_correct` (line 442).

The compact `PanValueControlResult` evaluator predates the clocked/FFI
boundary and therefore cannot express `TimeOut` or `FinalFFI`.  This module
keeps the existing source-to-Crep state, global, memory, exception, and
flattened-value relations, while adding those two result cases explicitly.
The evaluator obligations are parameters: the theorem below is the
kernel-checked assembly boundary to be discharged by the source and Crep
semantic proofs for each supported compiler subset.
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

/-! The explicit state/global/memory result relation.  The raised branch uses
the compiler-owned spill relation already used by the downstream Crep
correctness lemmas; timeout and FinalFFI retain the ordinary state relation. -/
def panValuePcResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
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
  | .raised _sourceLocals sourceGlobals sourceMemory sourceException sourceValue,
      .raised targetState targetException =>
      ∃ spillAddress,
        panValueCrepRaisedControlRel structs context exceptionRel
          sourceGlobals sourceMemory sourceException sourceValue targetState
          targetException spillAddress
  | .broke sourceLocals sourceGlobals sourceMemory, .broke targetState _ =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .continued sourceLocals sourceGlobals sourceMemory, .continued targetState _ =>
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

structure PanValuePcInput (α : Type u) where
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)

abbrev PanValuePcEvaluator (α : Type u) :=
  CompileContext α → PanValuePcInput α → Prog α → Option (PanValuePcResult α)

abbrev CrepPcEvaluator (α : Type u) :=
  CompileContext α → CrepState α → CrepProg α → Option (CrepPcResult α)

/-! The direct Lean analogue of the quantifier/implication shape of HOL
`pc_compile_correct`: related initial source/target state, successful source
and compiled-target evaluations, then the complete result relation. -/
def PanValuePcCompileCorrect
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (targetState : CrepState α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α),
    panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
      sourceInput.memory targetState →
    sourceEvaluate context sourceInput program = some sourceResult →
    targetEvaluate context targetState (compileProg context program) =
      some targetResult →
    panValuePcResultRel structs context exceptionRel sourceResult targetResult

/-! Packaging theorem for a supported compiler subset.  Every HOL result case
is an explicit obligation; in particular no proof can discharge this
boundary by silently dropping timeout or FinalFFI. -/
theorem panValuePcCompileCorrect_of_obligations
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (program : Prog α)
    (hobligation : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetState : CrepState α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α),
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetState →
      sourceEvaluate context sourceInput program = some sourceResult →
      targetEvaluate context targetState (compileProg context program) =
        some targetResult →
      panValuePcResultRel structs context exceptionRel sourceResult targetResult) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate program := by
  intro context structs sourceInput targetState exceptionRel sourceResult targetResult
    hstate hsource htarget
  exact hobligation context structs sourceInput targetState exceptionRel
    sourceResult targetResult hstate hsource htarget

end Flapjack
