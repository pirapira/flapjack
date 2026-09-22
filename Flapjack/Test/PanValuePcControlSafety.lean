import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.PanToCrepTailCallCorrectness
import Flapjack.PanToCrepCallHandlerControlSafety
import Flapjack.PanToCrepAssignmentControlSafety
import Flapjack.PanToCrepPrimitiveControlSafety
import Flapjack.PanToCrepPrimitiveCorrectness
import Flapjack.PanToCrepCallCorrectness
import Flapjack.PanToCrepCompileCorrectInduction
import Flapjack.PanToCrepConditionalCorrectness
import Flapjack.PanToCrepSharedMemoryControlSafety
import Flapjack.PanToCrepSharedMemoryCorrectness
import Flapjack.PanToCrepDeclarationControlSafety
import Flapjack.PanToCrepAssignmentCorrectness
import Flapjack.PanToCrepSequenceCorrectness
import Flapjack.PanToCrepLeafCorrectness
import Flapjack.PanToCrepAnnotCorrectness
import Flapjack.PanValueFfiClockCorrectness
import Flapjack.CrepeNestedDecsStability
import Flapjack.CrepeRaisedCallInversion
import Flapjack.PanToCrepDecCallCorrectness
import Flapjack.PanToCrepProgramComposition
import Flapjack.PanToCrepCodeRelation
import Flapjack.PanSimpLocalised

namespace Flapjack.Test.PanValuePcControlSafety

open Flapjack

/-! Regression for Cake's `state_rel_globals` projection: a related
    source-to-Crep state always has the empty source-global environment. -/
example
    (structs : StructContext) (context : CompileContext Nat)
    (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
    (sourceMemory : Nat → Option (PanValue Nat)) (state : CrepState Nat)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    sourceGlobals = (fun _ => none) :=
  panValueCrepStateRel_sourceGlobals_eq_none structs context sourceLocals
    sourceGlobals sourceMemory state hrel

/-! The context-coded `pc_compile_correct` boundary keeps the full
    evaluator/state/result obligation package explicit. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hobligation : ∀ (context : CompileContext Nat) (structs : StructContext)
      (sourceInput : PanValuePcInput Nat) (targetInput : CrepPcInput Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceExecution : PanValuePcExecution Nat)
      (targetExecution : CrepPcExecution Nat),
      sourceInput.structs = structs → targetInput.structs = structs →
      panValuePcLocalisedCode sourceInput.code → localisedProg program →
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
        globalsLookup sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate codeRel
      excpRel exceptionCode globalsLookup program := by
  exact panValuePcCompileCorrectWithContextCode_of_obligations sourceEvaluate
    targetEvaluate codeRel excpRel exceptionCode globalsLookup program hobligation

/-! The arbitrary context-coded evaluator path preserves the stronger result
    relation when the clocked source reaches a normal state. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram =
      some (.control (.normal clockLocals clockGlobals clockMemory clockFfi), clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.normal clockLocals clockGlobals clockMemory)
      (.normal clockTargetState) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_normal
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clockFuel clock clockLocals clockGlobals clockMemory
      clockFfi clockProgram clockTargetState hclock hclockState
  exact ⟨hresult.1, hresult.2.2.2⟩

example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (clockValues : List (PanValue Nat)) (clockTargetValues : List Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram =
      some (.control (.returned clockLocals clockGlobals clockMemory clockFfi
        clockValues), clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState)
    (hclockValues : panValueCrepValuesRel clockValues clockTargetValues) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.returned clockLocals clockGlobals clockMemory clockValues)
      (.returned clockTargetState clockTargetValues) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_returned
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clockFuel clock clockLocals clockGlobals clockMemory
      clockFfi clockProgram clockTargetState clockValues clockTargetValues
      hclock hclockState hclockValues
  exact ⟨hresult.1, hresult.2.2.2⟩

/-! The arbitrary context-coded evaluator path also preserves a clocked
    timeout without weakening the source/global result relation. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram =
      some (.timeout clockLocals clockGlobals clockMemory clockFfi, clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.timeout clockLocals clockGlobals clockMemory)
      (.timeout clockTargetState) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_timeout
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clockFuel clock clockLocals clockGlobals clockMemory
      clockFfi clockProgram clockTargetState hclock hclockState
  exact ⟨hresult.1, hresult.2.2.2⟩

/-! The arbitrary context-coded evaluator path preserves a terminal FFI event
    and its explicit target-state relation. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (event targetEvent : FfiFinalEvent) (finalFfi : FfiState Unit)
    (hclock : evalPanValueFfiClockLeaf clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clock clockLocals clockGlobals clockMemory clockFfi
      clockProgram =
      some (.control
        (.finalFfi clockLocals clockGlobals clockMemory finalFfi event), clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState)
    (hevent : event = targetEvent) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.finalFfi clockLocals clockGlobals clockMemory event)
      (.finalFfi clockTargetState targetEvent) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_final_ffi
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clock clockLocals clockGlobals clockMemory clockFfi
      clockProgram clockTargetState event targetEvent finalFfi hclock
      hclockState hevent
  exact ⟨hresult.1, hresult.2.2.2⟩

/-! The arbitrary context-coded evaluator path preserves a zero-label
    continued result and its explicit target-state relation. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram =
      some (.control (.continued clockLocals clockGlobals clockMemory clockFfi),
        clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.continued clockLocals clockGlobals clockMemory)
      (.continued clockTargetState 0) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_continued
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clockFuel clock clockLocals clockGlobals clockMemory
      clockFfi clockProgram clockTargetState hclock hclockState
  exact ⟨hresult.1, hresult.2.2.2⟩

/-! Generic raised evidence remains explicit at the arbitrary evaluator
    boundary rather than being replaced by a test-only proposition. -/
example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (clockException : ExceptionId) (clockValue : PanValue Nat)
    (clockTargetException : Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram =
      some (.control (.raised clockLocals clockGlobals clockMemory clockFfi
        clockException clockValue), clock))
    (hcontrol : panValueCrepControlRel clockStructs clockPcContext
      clockExceptionRel
      (.raised clockLocals clockGlobals clockMemory clockException clockValue)
      (.raised clockTargetState clockTargetException))
    (hevidence : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel clockStructs clockPcContext clockExceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel clockStructs clockPcContext sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode clockStructs clockPcContext
        clockExceptionRel clockExceptionCode clockGlobalsLookup
        sourceGlobals sourceMemory sourceException sourceValue targetState
        targetException) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup
      (.raised clockLocals clockGlobals clockMemory clockException clockValue)
      (.raised clockTargetState clockTargetException) := by
  have hresult :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_raised_evidence
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clockFuel clock clockLocals clockGlobals clockMemory
      clockFfi clockProgram clockTargetState clockException clockValue
      clockTargetException hclock hcontrol hevidence
  exact ⟨hresult.1, hresult.2.2.2⟩

example
    (sourceEvaluate : PanValuePcEvaluator Nat)
    (targetEvaluate : CrepPcEvaluator Nat)
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (program : Prog Nat)
    (hcompact : PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel
      excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext Nat)
    (clockExceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
    (clockExceptionCode : ExceptionId → Option Nat)
    (clockGlobalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (clockContext : PanValueFfiContext Nat)
    (clockPrimitive : PanPrimitiveHandler Nat)
    (clockHandler : PanValueStatefulFfiHandler Nat Unit)
    (clockFunctions : List (FunName × List VarName × Prog Nat))
    (clockBaseAddress clockTopAddress clockBytesInWord : Nat)
    (clockFuel clock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue Nat))
    (clockMemory : Nat → Option (PanValue Nat)) (clockFfi : FfiState Unit)
    (clockProgram : Prog Nat) (clockTargetState : CrepState Nat)
    (clockException : ExceptionId) (clockValue : PanValue Nat)
    (clockTargetException : Nat)
    (hclock : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi clock clockProgram = some
        (.control (.raised clockLocals clockGlobals clockMemory clockFfi
          clockException clockValue), clock))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState)
    (hclockRaise : panValuePcExceptionResultRel clockStructs clockPcContext
      clockExceptionRel clockExceptionCode clockGlobalsLookup clockGlobals
      clockMemory clockException clockValue clockTargetState clockTargetException) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program ∧
    panValuePcResultRel clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup
      (.raised clockLocals clockGlobals clockMemory clockException clockValue)
      (.raised clockTargetState clockTargetException) := by
  have hresult := panValuePcCompileCorrect_of_arbitrary_clocked_raised
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup program
    hcompact clockStructs clockPcContext clockExceptionRel clockExceptionCode
    clockGlobalsLookup clockContext clockPrimitive clockHandler clockFunctions
    clockBaseAddress clockTopAddress clockBytesInWord clockFuel clock clockLocals
    clockGlobals clockMemory clockFfi clockProgram clockTargetState clockException
    clockValue clockTargetException hclock hclockState hclockRaise
  exact ⟨hresult.1, hresult.2.2.2⟩

def controlContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

/-! The primitive control leaves satisfy the exact top-level Cake label rule. -/
example : PanValueCrepProgramStateControlSafe (.break : Prog Nat) :=
  panValueCrepProgramStateControlSafe_break

example : PanValueCrepProgramStateControlSafe (.continue : Prog Nat) :=
  panValueCrepProgramStateControlSafe_continue

/-! Cake's `pc_compile_correct[Return]` has no loop-control label to transport;
the source-word return bridge makes that case explicit. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.return (SourceWordExp.const (7 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.return (SourceWordExp.const (7 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_return_source_word
    (SourceWordExp.const 7) hbytesInWord hlookup

example :
    PanValueCrepProgramStateControlSafe
      (.seq (.break : Prog Nat) (.continue : Prog Nat)) := by
  exact panValueCrepProgramStateControlSafe_seq
    (.break : Prog Nat) (.continue : Prog Nat)
    panValueCrepProgramStateCorrect_break
    panValueCrepProgramStateControlSafe_break
    panValueCrepProgramStateControlSafe_continue

example (condition : SourceWordExp Nat) (thenBranch elseBranch : Prog Nat)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe
      (.ite condition.toExp thenBranch elseBranch) :=
  panValueCrepProgramStateControlSafe_ite_source_word condition thenBranch
    elseBranch hthenSafe helseSafe hbytesInWord hlookup

/-! The conditional bridge carries evaluator correctness and the boundary
    control-label obligation together. -/
example (condition : SourceWordExp Nat)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.ite condition.toExp (.break : Prog Nat) (.continue : Prog Nat)) ∧
      PanValueCrepProgramStateControlSafe
        (.ite condition.toExp (.break : Prog Nat) (.continue : Prog Nat)) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_ite_source_word
    condition (.break : Prog Nat) (.continue : Prog Nat)
    panValueCrepProgramStateCorrect_break
    panValueCrepProgramStateCorrect_continue
    panValueCrepProgramStateControlSafe_break
    panValueCrepProgramStateControlSafe_continue
    hbytesInWord hlookup

example (condition : SourceWordExp Nat) (body : Prog Nat)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body)) :
    PanValueCrepProgramStateControlSafe
      (.while condition.toExp body) :=
  panValueCrepProgramStateControlSafe_while_of_loop_safe condition body hloopSafe

example (body : Prog Nat) :
    PanValueCrepProgramLoopStateControlSafe
      (.while (SourceWordExp.const (0 : Nat)).toExp body) :=
  panValueCrepProgramLoopStateControlSafe_while_zero body

example (condition : SourceWordExp Nat) (body : Prog Nat)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body))
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.while condition.toExp body) ∧
      PanValueCrepProgramStateControlSafe (.while condition.toExp body) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_while_source_word
    condition body hbody hbodySafe hloopSafe hbytesInWord hlookup

/-! The store bridge carries evaluator correctness and the boundary
    control-label obligation together, with `hlookup`/`hstable` explicit. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState Nat) (baseAddress topAddress : Nat)
      (temporary : Nat) (compiled : CrepExp Nat) (value updateValue : Nat),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramStateCorrect
        (.store (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.store (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_store_source_word
    (SourceWordExp.const 7) (SourceWordExp.const 9) hbytesInWord hlookup hstable

/-! The paired fragment composes: a store followed by a control leaf carries
    both evaluator correctness and the control-label obligation together. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState Nat) (baseAddress topAddress : Nat)
      (temporary : Nat) (compiled : CrepExp Nat) (value updateValue : Nat),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramStateCorrect
        (.seq (.store (SourceWordExp.const (7 : Nat)).toExp
            (SourceWordExp.const (9 : Nat)).toExp) (.skip : Prog Nat)) ∧
      PanValueCrepProgramStateControlSafe
        (.seq (.store (SourceWordExp.const (7 : Nat)).toExp
            (SourceWordExp.const (9 : Nat)).toExp) (.skip : Prog Nat)) := by
  obtain ⟨hstoreCorrect, hstoreSafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_store_source_word
      (SourceWordExp.const 7) (SourceWordExp.const 9) hbytesInWord hlookup hstable
  exact panValueCrepProgramStateCorrect_and_controlSafe_seq _ _
    hstoreCorrect hstoreSafe
    panValueCrepProgramStateCorrect_skip
    panValueCrepProgramStateControlSafe_skip

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.store32 (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.store32 (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_store32_source_word
    (SourceWordExp.const 7) (SourceWordExp.const 9) hbytesInWord hlookup

example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.storeByte (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.storeByte (SourceWordExp.const (7 : Nat)).toExp
          (SourceWordExp.const (9 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_storeByte_source_word
    (SourceWordExp.const 7) (SourceWordExp.const 9) hbytesInWord hlookup

/-! The raise bridge carries evaluator correctness and the boundary
    control-label obligation together for a raised source word. -/
example
    (exception : ExceptionId)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext Nat),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext Nat) (state : CrepState Nat),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext Nat)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (value exceptionCode : Nat),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.word value) exceptionCode) :
    PanValueCrepProgramStateCorrect
        (.raise exception (SourceWordExp.const (9 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.raise exception (SourceWordExp.const (9 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_raise_source_word
    exception (SourceWordExp.const 9) hbytesInWord hlookup hlookupException
    hfresh hexception

/-! Nonzero labels remain rejected at the `pc_compile_correct` boundary. -/
example :
    ¬ panValuePcResultRel [] controlContext (fun _ _ _ => True) (fun _ => some 0)
        (fun _ _ => none)
        (.broke (fun _ => none) (fun _ => none) (fun _ => none))
        (.broke { locals := fun _ => none, memory := fun _ => none } 1) := by
  apply panValuePcResultRel_broke_rejects_nonzero_label
  decide

/-! Target-side freshness of the declaration prefix.  A list of freshly
allocated target locals preserves the state relation; with an empty variable
map the freshness side condition is vacuous.  This is the reusable ingredient
for the compiled store/declaration instances, whose programs start with
`nestedDecs`. -/
example :
    panValueCrepStateRel ([] : StructContext) controlContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := updateCrepLocalList (fun _ => none) [0, 1] [7, 9]
        memory := fun _ => none } := by
  have hrel : panValueCrepStateRel ([] : StructContext) controlContext
      (fun _ => none) (fun _ => none) (fun _ => none)
      { locals := fun _ => none, memory := fun _ => none } :=
    ⟨rfl, panValueCrepLocalsRel_empty _ _ _, rfl⟩
  exact panValueCrepStateRel_updateCrepLocalList_fresh
    ([] : StructContext) controlContext (fun _ => none) (fun _ => none)
    (fun _ => none) { locals := fun _ => none, memory := fun _ => none }
    [0, 1] [7, 9] hrel rfl
    (by
      intro name shape slots hlookup slot hslot
      simp [controlContext, lookupInfo] at hlookup)

/-! Threading the source state relation through the raised dispatcher. The bare
    control relation only exposes the except-spill memory relation and empty
    locals, so the state/code/lookup/shape obligations stay explicit. -/
set_option linter.unusedVariables false in
example
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (hpost : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory
        targetState)
    (hcode : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException :=
  panValuePcRaisedHraiseData_dispatch_of_state_rel exceptionCode globalsLookup
    hpost hcode hlookup hsize

/-! The generic raised-payload branch of the dispatcher can now be discharged
    from the same explicit state evidence, leaving only the concrete payload
    obligations `hword`/`htwo`/`hthree` to the caller. -/
set_option linter.unusedVariables false in
example
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (hword : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (value : Nat) (targetState : CrepState Nat) (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.word value) targetState targetException)
    (htwo : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (left right : Nat) (targetState : CrepState Nat) (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word left, .word right]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word left, .word right]) targetState targetException)
    (hthree : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (first second third : Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException)
    (hpost : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals sourceMemory
        targetState)
    (hcode : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException :=
  panValuePcRaisedHraiseCases_of_state_evidence exceptionCode globalsLookup
    hword htwo hthree hpost hcode hlookup hsize

/- The context-code state-evidence wrapper is available at the expected
signature (no opaque raised-data obligation). -/
#check @panValuePcCompileCorrect_compact_with_raised_state_evidence_context_code

/- The concrete one-word-record raise instance also drops the opaque
evaluator-evidence obligation. -/
#check @panValuePcCompileCorrect_compact_one_word_raise_of_state_evidence

/- The two-word-record raise instance composes the same boundary with the
   two-word Cake program-control theorem. -/
#check @panValuePcCompileCorrect_compact_two_word_raise_of_state_evidence

/- The three-word-record instance uses the corresponding Cake-shaped
   program-control theorem and the same explicit raised-state evidence. -/
#check @panValuePcCompileCorrect_compact_three_word_raise_of_state_evidence

/- The four-word-record instance extends the same Cake-faithful construction
   to the final fixed-width record payload. -/
#check @panValuePcCompileCorrect_compact_four_word_raise_of_state_evidence
#check @panValuePcCompileCorrect_compact_word_list_raise_of_state_evidence

/- The context-coded word-list raise instance uses the same state evidence and
   additionally returns the context-coded correctness boundary. -/
#check @panValuePcCompileCorrect_compact_word_list_raise_of_state_evidence_context_code

/- The source-word and nested one-word-record raise instances also drop the
   opaque evaluator-evidence obligation in favour of explicit state evidence. -/
#check @panValuePcCompileCorrect_compact_raise_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_nested_one_word_raise_of_state_evidence
#check @panValuePcCompileCorrect_compact_nested_one_word_raise_of_state_evidence_context_code

/- The context-coded source-word raise instance uses the same state evidence and
   additionally returns the context-coded correctness boundary. -/
#check @panValuePcCompileCorrect_compact_raise_source_word_of_state_evidence_context_code

/- The raw-word-list dispatcher also has a state-evidence form that discharges the
   generic `hother` branch without an opaque raised-data obligation. -/
#check @panValuePcRaisedHraiseCases_with_raw_word_lists_of_state_evidence
#check @panValuePcCompileCorrect_compact_with_raw_word_lists_context_code_of_state_evidence
#check @panValuePcCompileCorrect_compact_ite_source_word_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_while_source_word_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_while_source_word_of_state_evidence_context_code_and_clocked
#check @panValuePcCompileCorrect_of_compact_evaluators_with_expression_state_evidence_and_clocked_raised
#check @panValuePcCompileCorrect_of_compact_evaluators_with_expression_state_evidence_and_clocked_timeout
#check @panValuePcCompileCorrect_of_compact_evaluators_with_expression_state_evidence_and_clocked_final_ffi
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_raised
#check @panValuePcCompileCorrectWithContextCode_compact_with_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_raised
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_timeout
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_final_ffi
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_returned
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_continued
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_broke
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_normal

/- The arbitrary word-list Raise bridge preserves the same explicit clocked
   evaluator and state/result premises at the top-level boundary. -/
#check @panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_word_list_raise_context_code_and_clocked
/- The fixed-width and nested-record raise instances also have context-coded
   state-evidence forms returning the context-coded correctness boundary. -/
#check @panValuePcCompileCorrect_compact_one_word_raise_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_two_word_raise_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_three_word_raise_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_four_word_raise_of_state_evidence_context_code

/-! The plain exception-result dispatcher likewise accepts the explicit
    state-evidence premises instead of the opaque raised-payload callback. -/
#check @panValuePcRaisedHraiseCases_to_exception_result_rel_of_state_evidence

/-! The context-coded exception-result dispatcher also accepts the explicit
    state-evidence premises instead of the opaque raised-payload callback. -/
#check @panValuePcRaisedHraiseCases_to_exception_result_rel_with_context_code_of_state_evidence
/-! The paired raw-word-list dispatcher also accepts the explicit state
    evidence plus the exception lookup instead of the opaque callbacks. -/
#check @panValuePcRaisedHraiseCases_with_raw_word_lists_paired_of_state_evidence

/-! The plain (non-context-coded) store state-evidence instances are the
    companions used by the ordinary compact correctness boundary. -/
#check @panValuePcCompileCorrect_compact_store_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_store32_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_storeByte_source_word_of_state_evidence

/-! The plain (non-context-coded) conditional and loop wrappers accept the
    explicit state evidence instead of the opaque evaluator callback. -/
#check @panValuePcCompileCorrect_compact_ite_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_while_source_word_of_state_evidence

/-! The expression-parametric `Return` wrappers also accept explicit
    state evidence in plain and context-coded form. -/
#check @panValuePcCompileCorrect_compact_return_of_state_evidence
#check @panValuePcCompileCorrect_compact_return_with_context_code_of_state_evidence
#check @panValuePcCompileCorrect_compact_return_with_context_code_of_state_evidence_and_clocked

/-! The plain raw-word-list entrypoint also accepts explicit state evidence
    for the generic `hother` callback. -/
#check @panValuePcCompileCorrect_compact_with_raw_word_lists_of_state_evidence

/-! The source-word-record raise wrappers also accept explicit state evidence in
    plain and context-coded form. -/
#check @panValuePcCompileCorrect_compact_source_word_record_raise_of_state_evidence
#check @panValuePcCompileCorrect_compact_source_word_record_raise_of_state_evidence_context_code

/-! The retargeted-globals raw-word dispatcher also accepts explicit state
    evidence for the generic hother callback. -/
#check @panValuePcRaisedHraiseCases_with_raw_word_lists_retarget_globals_of_state_evidence

/-! The raw-word-list context-coded exception-result dispatcher also accepts
    explicit state evidence. -/
#check @panValuePcRaisedHraiseCases_with_raw_word_lists_to_exception_result_rel_with_context_code_of_state_evidence

/-! The handler-free call form discharges the control-safety premise of the
compact Pc bridge directly, without an opaque evaluator-evidence argument. -/
#check @panValueCrepProgramStateControlSafe_call_none

#check @panValueCrepProgramStateControlSafe_call_returns

/-! A handler-free call now has one paired induction branch: arbitrary
    state/evaluator evidence supplies simulation, while the call safety proof
    supplies the final label-zero obligation. -/
#check @panValueCrepProgramStateCorrect_and_controlSafe_call_none_of_relation

#check @panValueCrepProgramStateCorrect_and_controlSafe_call_returns_of_relation

/-! Declaration calls now expose the paired state simulation and control-safety
    package used by Pancake's `pc_compile_correct[DecCall]` branch. -/
#check @panValueCrepDecCall_state_and_controlSafe_of_body

#check @panValueCrepProgramStateCorrect_and_controlSafe_call_handler_of_relation

/-! A call whose metadata carries an exception handler needs explicit handler
    safety: a handler program that never returns a loop-control result.  The
    source-side never-broke-continued predicate and the resulting control-safety
    theorem make that premise explicit. -/
#check @PanValueProgNotBrokeContinued
#check @evalPanValueCallWithPrimitiveCallsAndFfi_handler_not_broke_continued
#check @panValueCrepProgramStateControlSafe_call_handler
/-! The source-level handler-safety predicate is closed under leaves,
    sequences, and conditionals, and it yields the handler-carrying decCall
    control-safety instance. -/
#check @PanValueProgNotBrokeContinued_skip
#check @PanValueProgNotBrokeContinued_seq
#check @PanValueProgNotBrokeContinued_ite
#check @PanValueProgNotBrokeContinued_return
#check @PanValueProgNotBrokeContinued_raise
#check @panValueCrepProgramStateControlSafe_decCall

/-! The "exception id in handler not found in context" sub-case of Cake's
    `Call_Ret_Exception` branch: when the handler's exception is absent from
    the compile context, the emitted call drops the handler metadata.  These
    equations expose the standalone and both destination-carrying degraded
    shapes as explicit compile-side premises. -/
#check @compileProg_call_handler_missing_of_compiled
#check @compileProg_call_handler_missing_destination_degraded_of_compiled
#check @compileProg_call_handler_missing_destination_of_compiled

#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_handler
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_handler_destination
#check @evalPanValueFfiClockProg_call_caught_handler_destination
/-! The `Call_Ret` branch of Cake's `pc_compile_correct`: the
    assignment-producing call with no handler keeps the flattened destination
    slots when `wrap_rt` preserves the shape, and degrades to a tail call
    otherwise.  These equations expose both emitted shapes. -/
#check @compileProg_call_destination_of_compiled
#check @compileProg_call_destination_degraded_of_compiled
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_handler_raised
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_handler_raised
#check @panValueCrepProgramStateCorrect_and_controlSafe_call_handler_return_of_relation
#check @panValueCrepProgramStateCorrect_and_controlSafe_call_handler_raise_of_relation
#check @panValueCrepProgramStateControlSafe_decCall_return
#check @panValueCrepProgramStateControlSafe_decCall_raise

/-! The caught-handler call exposes the outer-to-inner handler branch: when the
    callee raises with a matching code, the call's crep result is exactly the
    handler program's evaluation from the handler-entry state. -/
#check @evalCrepFullCallState_raised_handler_of_callee

/-! The direct `Call_Ret_FinalFFI` branch of Cake's `pc_compile_correct`: a
    direct call propagates the callee's terminal FFI event unchanged. -/
#check @panValuePcFinalFfiResultRel_of_clocked_call
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_finalFfi
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_finalFfi
#check @panValuePcRaisedResultRelWithContextCode_of_clocked_call
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_raised_no_handler
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_raised
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_returned_no_handler
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_returned_no_handler
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_tailCall
#check @panValuePcCompileCorrect_of_clocked_call_tailCall
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_returned_destination
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_returned_destination
/-! Compositional source handler safety: a handler-free call and a declaration
    body that never exposes loop control. -/
#check @PanValueProgNotBrokeContinued_call_of_no_handler
#check @PanValueProgNotBrokeContinued_call_handler
#check @PanValueProgNotBrokeContinued_dec

/-! The direct `Call_Ret_Exception` branch of Cake's `pc_compile_correct`: a
    direct call propagates the callee's uncaught raise unchanged. -/
#check @panValuePcRaisedResultRelWithContextCode_of_clocked_call

/-! The `DecCall` timeout lift: a declaration call whose callee runs out of
    clock crosses the enclosing program boundary as a `timeout` outcome. -/
#check @panValuePcTimeoutResultRel_of_clocked_decCall

/-! The direct `Call_Ret` timeout lift: a direct call whose callee runs out of
    clock crosses the enclosing program boundary as a `timeout` outcome. -/
#check @panValuePcTimeoutResultRel_of_clocked_call
#check @panValuePcCompileCorrectWithContextCode_of_compact_and_caught_call
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_broke
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_raised
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_timeout
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_timeout
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_returned
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_returned_finalFfi
#check @panValuePcCompileCorrect_of_context_code_and_clocked_decCall_returned_finalFfi
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_returned_value
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_extCall_finalFfi
#check @panValuePcCompileCorrect_of_context_code_and_clocked_extCall_finalFfi_state
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_extCall_finalFfi_state
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_extCall_finalFfi_stateful

/-! Declaration-call counterparts of the direct-call compositional bridges:
    terminal FFI, uncaught raise, and timeout, each preserving explicit
    state/observation premises. -/
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_finalFfi
#check @panValuePcCompileCorrect_of_context_code_and_clocked_decCall_finalFfi
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_raised
#check @panValuePcCompileCorrect_of_context_code_and_clocked_decCall_raised
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_timeout
#check @panValuePcCompileCorrect_of_context_code_and_clocked_decCall_timeout

/-! Declaration-call result theorem for the `shape_of v ≠ return_sh` sub-case:
    a declaration call whose callee returns a wrong-shaped value evaluates to
    `none`, so the source side of Cake's `DecCall` resume is vacuous. -/
#check @evalPanValueFfiClockProg_decCall_shape_mismatch

/-! More compositional source handler-safety leaves: clock, annotation, local
    assignment, and single-word store. -/
#check @PanValueProgNotBrokeContinued_tick
#check @PanValueProgNotBrokeContinued_annot
#check @PanValueProgNotBrokeContinued_assign_local
#check @PanValueProgNotBrokeContinued_store

/-! More source handler-safety leaves: global assignment, primitive call, and
    32/8-bit stores. -/
#check @PanValueProgNotBrokeContinued_assign_global
#check @PanValueProgNotBrokeContinued_primitive
#check @PanValueProgNotBrokeContinued_store32
#check @PanValueProgNotBrokeContinued_storeByte

/-! The original Pancake `ExtCall` branch accepts arbitrary word expressions;
    this generalized context-coded bridge carries their source-word and
    temporary-slot obligations into `pc_compile_correct`. -/
#check @panValueCrepProgramStateControlSafe_extCall_wordExp
#check @panValuePcCompileCorrectWithContextCode_compact_extCall_wordExp

/-! More source handler-safety leaves: external calls and shared-memory
    load/store. -/
#check @PanValueProgNotBrokeContinued_extCall
#check @PanValueProgNotBrokeContinued_shMemLoad
#check @PanValueProgNotBrokeContinued_shMemStore

/-! A concrete caught-handler body (local assignment then raise) discharges
    compositionally from the individual source-safety leaves. -/
example :
    PanValueProgNotBrokeContinued (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
      (.seq (.assign VarKind.local "x" (.const 9)) (.raise "E" (.const 0))) :=
  PanValueProgNotBrokeContinued_seq (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
    (.assign VarKind.local "x" (.const 9)) (.raise "E" (.const 0))
    (PanValueProgNotBrokeContinued_assign_local (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
      "x" (.const 9))
    (PanValueProgNotBrokeContinued_raise (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat) "E" (.const 0))

#check @PanValueProgNotBrokeContinued_while

#check @PanValueProgNotBrokeContinued_decCall
#check @PanValueProgNotBrokeContinued_smartSeq
#check @PanValueProgNotBrokeContinued_seqCallRet

/-! A declaration call whose body is safe is itself safe. -/
example :
    PanValueProgNotBrokeContinued (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
      (.decCall "x" .one "f" [] (.skip : Prog Nat)) :=
  PanValueProgNotBrokeContinued_decCall (fun _ _ => none)
    (fun _ _ _ _ _ _ => none) ([] : StructContext) [] (0 : Nat) (0 : Nat)
    (1 : Nat) "x" .one "f" [] (.skip : Prog Nat)
    (PanValueProgNotBrokeContinued_skip (fun _ _ => none)
      (fun _ _ _ _ _ _ => none) ([] : StructContext) [] (0 : Nat) (0 : Nat)
      (1 : Nat))

/-! A while loop over a safe body is discharged by the recursive while leaf. -/
example :
    PanValueProgNotBrokeContinued (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
      (.while (.const 0) (.skip : Prog Nat)) :=
  PanValueProgNotBrokeContinued_while (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat) (.const 0) (.skip : Prog Nat)
    (PanValueProgNotBrokeContinued_skip (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat))

/-! The handler-carrying call leaf is dischargeable when the handler is `.skip`. -/
example :
    PanValueProgNotBrokeContinued (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
      (.call (some (some (VarKind.local, "r"), some ("E", "x", (.skip : Prog Nat))))
        "f" []) :=
  PanValueProgNotBrokeContinued_call_handler (fun _ _ => none)
    (fun _ _ _ _ _ _ => none) ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat)
    (some (some (VarKind.local, "r"), some ("E", "x", (.skip : Prog Nat)))) "f" []
    (by
      intro handlerProgram hinfo
      obtain ⟨destination, caught, handlerVariable, hinfoEq⟩ := hinfo
      cases hinfoEq
      exact PanValueProgNotBrokeContinued_skip (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) ([] : StructContext) [] (0 : Nat) (0 : Nat) (1 : Nat))

/-! The explicit handler-safety premise of the handler-carrying call control
    theorem is dischargeable for a concrete call: choose a call whose handler is
    `.skip`, so the premise reduces to the skip leaf. -/
example :
    PanValueCrepProgramStateControlSafe
      (.call (some (some (VarKind.local, "r"), some ("E", "x", (.skip : Prog Nat))))
        "f" []) :=
  panValueCrepProgramStateControlSafe_call_handler _ _ _
    (by
      intro primitive sourceHandler structs sourceFunctions baseAddress topAddress
        bytesInWord handlerProgram hinfo
      obtain ⟨destination, caught, handlerVariable, hinfoEq⟩ := hinfo
      cases hinfoEq
      exact PanValueProgNotBrokeContinued_skip primitive sourceHandler structs
        sourceFunctions baseAddress topAddress bytesInWord)

/-! The Crep-side control-safety predicate cannot be exchanged for the source
    handler-safety predicate: `.break` is control-safe on both sides but still
    yields a `broke` source result. -/
#check @not_panValueProgNotBrokeContinued_break

/-! Shared-memory leaves are control-safe: the source evaluator can only
    produce `normal`, so the label rule holds for every `VarKind`. -/
#check @panValueCrepProgramStateControlSafe_shMemLoad
#check @panValueCrepProgramStateControlSafe_shMemStore
#check @panValueCrepProgramStateCorrect_and_controlSafe_shMemLoad_source_word
#check @panValueCrepProgramStateCorrect_and_controlSafe_shMemStore_source_word
#check @panValuePcCompileCorrect_compact_shMemLoad_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_shMemStore_source_word_of_state_evidence
#check @panValueCrepProgramStateControlSafe_dec
#check @panValuePcCompileCorrect_compact_dec_of_state_evidence
#check @panValueCrepProgramStateControlSafe_assign_local
#check @panValuePcCompileCorrect_compact_assign_local_source_word_of_state_evidence
#check @panValuePcCompileCorrect_compact_assign_of_state_evidence
#check @panValuePcCompileCorrect_compact_seq_of_state_evidence
#check @panValuePcCompileCorrect_compact_tick
#check @panValuePcCompileCorrect_compact_annot
#check @panValuePcCompileCorrectWithContextCode_compact_with_generalized_flat_global_evaluator_evidence_and_clocked_control
#check @panValuePcCompileCorrectWithContextCode_compact_with_generalized_flat_global_evaluator_evidence_and_clocked_raised
#check @panValuePcCompileCorrectWithContextCode_compact_with_concrete_flat_global_evaluator_evidence_and_clocked_raised
#check @panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_compiled_raise_canonical_globals
#check @panValuePcCompileCorrect_compact_with_generalized_clocked_raised_context_projection
#check @panValuePcCompileCorrect_compact_with_concrete_flat_global_evaluator_evidence_and_clocked_raised_projection
#check @panValuePcCompileCorrect_compact_with_generalized_clocked_normal_context_projection
#check @panValuePcCompileCorrect_compact_break
#check @panValuePcCompileCorrect_compact_continue
#check @panValuePcCompileCorrect_compact_annot
#check @panValuePcCompileCorrect_compact_shMemLoad_source_word
#check @panValuePcCompileCorrect_compact_shMemStore_source_word
#check @panValueCrepProgramStateControlSafe_assign
#check @panValueCrepProgramStateControlSafe_primitive
#check @panValuePcCompileCorrect_compact_primitive_of_state_evidence
#check @panValuePcCompileCorrect_compact_call_of_state_evidence
#check @panValuePcCompileCorrect_compact_decCall_of_state_evidence
#check @panValuePcCompileCorrect_compact_extCall_of_state_evidence
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_handler_returned
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_handler_returned
#check @panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_handler_normal
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_handler
#check @panValuePcCompileCorrect_of_context_code_and_clocked_call_handler_destination
#check @panValuePcCompileCorrect_of_context_code_and_clocked_decCall_returned_value
#check @panValueProg_compile_correct_induction
#check @panValuePcCompileCorrect_compact_of_constructor_induction
#check @panValuePcCompileCorrectWithContextCode_compact_of_constructor_induction
#check @panValuePcCompileCorrect_compact_ite_word_exp_of_state_evidence_context_code
#check @panValuePcCompileCorrect_compact_while_word_exp_of_state_evidence_context_code

#check @panValuePcResultRel_rejects_source_error
#check @panValuePcResultRel_rejects_target_error
#check @panValuePcResultRel_rejects_normal_returned
#check @panValuePcResultRel_rejects_broke_continued
#check @panValuePcResultRel_rejects_timeout_normal
#check @panValuePcResultRel_rejects_finalFfi_normal
#check @panValuePcResultRel_constructor_eq

#check @panValuePcCompileCorrect_compact_of_state_and_control_safe_induction

#check @panValuePcResultRel_normal_iff
#check @panValuePcResultRel_returned_iff
#check @panValuePcResultRel_broke_iff
#check @panValuePcResultRel_continued_iff
#check @panValuePcResultRel_timeout_iff
#check @panValuePcResultRel_finalFfi_iff
#check @panValuePcResultRel_raised_iff
#check @panValuePcResultRelWithContextCode_raised_iff
#check @panValuePcResultRelWithContextCode_normal_iff
#check @panValuePcResultRelWithContextCode_returned_iff
#check @panValuePcResultRelWithContextCode_broke_iff
#check @panValuePcResultRelWithContextCode_continued_iff
#check @panValuePcResultRelWithContextCode_timeout_iff
#check @panValuePcResultRelWithContextCode_finalFfi_iff
#check @panValuePcExceptionResultRelWithContextCode_of_rel_and_lookup
#check @panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
#check @panValuePcResultRelWithContextCode_broke_rejects_nonzero_label
#check @panValuePcResultRelWithContextCode_continued_rejects_nonzero_label
#check @panValuePcResultRelWithContextCode_constructor_eq
#check @panValuePcResultRelWithContextCode_rejects_source_error
#check @panValuePcResultRelWithContextCode_rejects_target_error
#check @panValuePcExceptionResultRel_of_withContextCode
#check @panValuePcResultRel_of_withContextCode
#check @panValuePcCompileCorrect_of_withContextCode
#check @panValuePcCompileCorrect_of_context_code_obligations
#check @panValuePcCompileCorrect_compact_with_expression_state_evidence_canonical_globals
#check @panValueCrepExpressionStateEvidence_of_correct_with_bounded_vars

/-! Concrete kernel-checked instantiation of the fragment-restricted
    composition: the `StatefulCompactProg` program `return 7; tick` yields the
    plain compact `pc_compile_correct` boundary, with the raised-state premises
    kept explicit.  This exercises the paired fragment induction rather than
    only restating the generic composition theorem. -/
set_option linter.unusedVariables false in
example
    (codeRel : PanValuePcCodeRel Nat)
    (excpRel : PanValuePcExceptionShapeRel Nat)
    (exceptionCode : ExceptionId → Option Nat)
    (globalsLookup : CrepState Nat → PanValue Nat → Option (List Nat))
    (primitive : PanPrimitiveHandler Nat)
    (sourceHandler : PanValueFfiHandler Nat)
    (crepPrimitive : CrepPrimitiveHandler Nat)
    (ffi : CrepFfiHandler Nat)
    (sharedMem : CrepSharedMemHandler Nat)
    (baseAddress topAddress bytesInWord : Nat)
    (sourceFuel targetFuel : Nat)
    (hpost : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState)
    (hcode : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext Nat) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue Nat → Nat → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
      (sourceMemory : Nat → Option (PanValue Nat)) (sourceException : ExceptionId)
      (sourceValue : PanValue Nat) (targetState : CrepState Nat)
      (targetException : Nat),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler []
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator [] crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.seq (.return (.const 7)) (.tick : Prog Nat)) :=
  panValuePcCompileCorrect_compact_statefulCompact
    (.seq (.return (.const 7)) (.tick : Prog Nat))
    (StatefulCompactProg.seq (StatefulCompactProg.returnConst 7)
      StatefulCompactProg.tick)
    codeRel excpRel exceptionCode globalsLookup [] [] primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord sourceFuel
    targetFuel hpost hcode hlookup hsize

#check @panValuePcCompileCorrect_compact_statefulCompact
#check @panValuePcCompileCorrect_compact_statefulCompact_canonical_globals
#check @panValuePcCompileCorrect_compact_statefulCompact_context_code
#check @panValuePcRaisedBoundedExpressionEvidence
#check @panValuePcRaisedBoundedGenericEvidence
#check @panValuePcRaisedBoundedExceptionResultRelWithContextCode
#check @panValuePcClockedRaisedExceptionResultRel_of_bounded_evidence
#check @panValuePcCompileCorrect_of_arbitrary_clocked_raised_with_bounded_evidence
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_timeout
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_final_ffi
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_returned
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_normal
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_broke
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_evidence_and_clocked_continued
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_generic_raised_evidence_and_clocked_control
#check @panValuePcCompileCorrect_of_compact_evaluators_with_bounded_generic_raised_evidence_and_clocked_raised
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_bounded_generic_raised_evidence_and_clocked_raised
#check @panValuePcCompileCorrectWithContextCode_of_arbitrary_clocked_raised_with_bounded_evidence
#check @panValuePcCompileCorrect_compact_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_with_bounded_expression_state_evidence_canonical_globals
#check @panValuePcCompileCorrect_compact_one_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_two_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_three_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_four_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_word_list_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_raise_source_word_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_with_expression_state_evidence_canonical_globals
#check @panValuePcCompileCorrectWithContextCode_compact_one_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_two_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_three_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_four_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_word_list_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_raise_source_word_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrectWithContextCode_compact_nested_one_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_compact_nested_one_word_raise_with_bounded_expression_state_evidence
#check @panValuePcCompileCorrect_of_compact_evaluators_and_clocked_word_raise_hraise_data
#check @panValuePcCompileCorrect_of_compact_evaluators_and_clocked_two_word_raise_hraise_data
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_and_clocked_raised_control_evidence
#check @panValuePcCompileCorrect_of_compact_evaluators_and_clocked_raised_control_evidence
#check @panValuePcCompileCorrectAndClockedResultRel_of_context_code
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_context_code
#check @panValuePcCompileCorrectAndRaisedResultRel_of_hraise_data
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_hraise_data
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_control_evidence
#check @panValuePcCompileCorrectAndClockedTimeoutResultRel_of_context_code
#check @panValuePcCompileCorrectWithContextCodeAndClockedTimeoutResultRel_of_state
#check @panValuePcCompileCorrectAndClockedFinalFfiResultRel_of_context_code
#check @panValuePcCompileCorrectAndClockedReturnedResultRel_of_context_code
#check @panValuePcCompileCorrectAndClockedReturnedResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedNormalResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedBrokeResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedContinuedResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedNormalResultRel_of_context_code
#check @panValuePcCompileCorrectAndClockedBrokeResultRel_of_context_code
#check @panValuePcCompileCorrectAndClockedContinuedResultRel_of_context_code
#check @panValueCrepControlRel_of_program_state_correct
#check @panValueCrepClockControlRel_of_program_state_correct
#check @panValuePcCompileCorrect_of_context_code_and_clocked_control_of_program_state_correct
#check @panValuePcClockedRaisedHraiseData_of_program_state_correct
#check @panValuePcClockedRaisedExceptionResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_clocked_program_state_correct
#check @panValuePcCompileCorrectAndClockedTimeoutResultRel_of_normal_program_state_correct
#check @panValuePcCompileCorrectAndClockedFinalFfiResultRel_of_normal_program_state_correct
#check @panValuePcCompileCorrectAndResultRel_of_context_code
#check @panValuePcCompileCorrectAndRaisedResultRel_of_context_code

/-! The scalar `wordExp` return also satisfies the control-safety obligation,
via the `SourceWordExp` conversion. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe (.return (.const 7)) :=
  panValueCrepProgramStateControlSafe_return_wordExp (.const 7) trivial
    hbytesInWord hlookup

/-! The scalar `wordExp` conditional and while cases also lift. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe
      (.ite (.const 5) (.return (.const 7)) (.tick : Prog Nat)) :=
  panValueCrepProgramStateControlSafe_ite_wordExp (.const 5) trivial
    (.return (.const 7)) (.tick : Prog Nat)
    (panValueCrepProgramStateControlSafe_return_wordExp (.const 7) trivial
      hbytesInWord hlookup)
    panValueCrepProgramStateControlSafe_tick
    hbytesInWord hlookup

#check @panValueCrepProgramStateControlSafe_while_wordExp

/-! The concrete Cake `code_rel` analogue is an inhabitant of the abstract
`PanValuePcCodeRel` parameter, so it can be supplied directly to
`pc_compile_correct`. -/
example (context : CompileContext Nat) (target : PanValuePcTargetCode Nat) :
    panValuePcCodeRelConcrete context [] target :=
  panValuePcCodeRelConcrete_nil context target

#check @panValuePcCodeRelConcrete
#check @panValuePcCodeRelConcrete_localised

/-! The concrete Cake `excp_rel` analogue is likewise an inhabitant of the
abstract `PanValuePcExceptionShapeRel` parameter. -/
example (context : CompileContext Nat) (eshapes : InfoMap Shape) :
    panValuePcExceptionShapeRelConcrete context eshapes eshapes :=
  panValuePcExceptionShapeRelConcrete_refl context eshapes

#check @panValuePcExceptionShapeRelConcrete
#check @panValuePcExceptionShapeRelConcrete_refl
#check @panValuePcExceptionShapeRelConcrete_of_declaration_evaluation

#check @lookupPanFunction_mem
#check @panValuePcLocalisedCode_lookup

/-! Cake's `ctxt_max_def`/`no_overlap_def` (`pan_commonPropsScript.sml:11,18`)
are ported as concrete predicates on the variable map, with the empty map as a
kernel-checked inhabitant. -/
#check @panValueCtxtMax
#check @panValueNoOverlap
#check @panValueCtxtMax_empty
#check @panValueNoOverlap_empty
#check @panValueNoOverlap_lookup_disjoint

/-- Regression for Cake `no_overlap_flookup_distinct`: the lemma is applicable
to any `no_overlap` variable map with two distinct looked-up variables. -/
example (name name' : String) (shape shape' : Shape) (slots slots' : List Nat)
    (hne : name ≠ name')
    (hlookup : lookupInfo name ([] : InfoMap (Shape × List Nat)) =
      some (shape, slots))
    (hlookup' : lookupInfo name' ([] : InfoMap (Shape × List Nat)) =
      some (shape', slots')) :
    ListDisjoint slots slots' :=
  panValueNoOverlap_lookup_disjoint
    ([] : InfoMap (Shape × List Nat)) name name' shape shape' slots slots'
    panValueNoOverlap_empty hne hlookup hlookup'

#check @panValueNoOverlap_zip_withShape

/-- Regression for Cake `all_distinct_alist_no_overlap`: splitting a nodup flat
    slot list across a two-component shape yields a `no_overlap` alist. -/
example :
    panValueNoOverlap
      ((["a", "b"] : List VarName).zip
        (([Shape.one, Shape.one] : List Shape).zip
          (withShape [Shape.one, Shape.one] [0, 1]))) :=
  panValueNoOverlap_zip_withShape [0, 1] ["a", "b"]
    [Shape.one, Shape.one] (by decide) (by simp [Shape.shapeSize]) (by decide)

#check @panValueCtxtMax_compileParamVars
#check @panValueNoOverlap_compileParamVars

/-! The generated formal-parameter context satisfies the two Cake invariants
    used by `locals_rel`, with the original source-shaped maximum convention.
    These examples keep the construction executable while checking the
    theorem-level bridge on both scalar and structured parameters. -/
private def parameterContextFixture : List (VarName × Shape) :=
  [("word", .one), ("pair", .comb [.one, .one]), ("empty", .comb [])]

example :
    panValueNoOverlap (panToCrepMakeVmap parameterContextFixture) := by
  simpa [panToCrepMakeVmap] using
    panValueNoOverlap_compileParamVars parameterContextFixture 0

example :
    panValueCtxtMax
      (Shape.shapeSize (.comb (parameterContextFixture.map Prod.snd)) - 1)
      (panToCrepMakeVmap parameterContextFixture) := by
  have hnames : (parameterContextFixture.map Prod.fst).Nodup := by
    simp [parameterContextFixture]
  have h := panValueCtxtMax_compileParamVars parameterContextFixture 0 hnames
  rw [compileParamVars_next_offset] at h
  simpa [panToCrepMakeVmap] using h

/-! The concrete `code_rel` analogue is non-vacuous on a source-faithful,
nonempty function table: instantiating Cake's `mk_ctxt_code_imp_code_rel` port
on a single declaration whose body is a localised `skip`. -/
private def concreteRelContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

private def concreteRelDecls : List (Decl Nat) :=
  [Decl.function { name := "f", inline := false, exported := false, params := [], body := (.skip : Prog Nat), returnShape := .one }]

example :
    panValuePcCodeRelConcrete
      { concreteRelContext with functions := functionInfos concreteRelDecls }
      (sourceFunctionEntries concreteRelDecls)
      (compileToCrep concreteRelContext concreteRelDecls) :=
  panValuePcCodeRelConcrete_compileToCrep concreteRelContext concreteRelDecls (by
    intro entry hentry
    simp [concreteRelDecls, sourceFunctionEntries] at hentry
    rcases hentry with rfl
    exact localisedProg_skip)

#check @panValuePcCodeRelConcrete_compileToCrep
#check @panValuePcRaisedHraiseData_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_program_state_correct
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_both_program_state_correct
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_hraise_data_with_clock_context
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_clocked_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedRaisedResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectWithContextCode_of_compact_evaluators_with_expression_state_evidence_and_clocked_raised_control_evidence
#check @panValuePcCompileCorrectAndClockedReturnedResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedNormalResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedResultRel_of_program_state_correct_with_context_code
#check @panValuePcCompileCorrectAndClockedBrokeResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedContinuedResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedTimeoutResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndClockedResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcRaisedHraiseData_callback_to_control_exception_result_rel_with_context_code
#check @panValuePcCompileCorrectAndClockedFinalFfiResultRel_of_both_program_state_correct_with_clock_context
#check @panValuePcCompileCorrectAndResultRel_of_program_state_correct_with_context_code
#check @panValuePcCompileCorrectAndRaisedResultRel_of_program_state_correct_with_context_code
#check @panValuePcCompileCorrectAndClockedResultRel_of_normal_program_state_correct_with_context_code
#check @panValuePcCompileCorrectAndClockedReturnedSourceResultRel_of_program_state_correct_with_context_code
#check @panValuePcRaisedHraiseData_of_flat_global_evaluator_evidence_with_bounded_state_locals
#check @panValuePcRaisedControlResultRel_callback_of_flat_global_evaluator_evidence_bounded_state_locals
#check @panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_bounded_state_locals
#check @panValuePcNormalResultRelWithContextCode_of_program_state_correct
#check @panValuePcReturnedResultRelWithContextCode_of_program_state_correct
#check @panValuePcBrokeResultRelWithContextCode_of_program_state_correct
#check @panValuePcContinuedResultRelWithContextCode_of_program_state_correct

/-! Cake's generated parameter context satisfies the slot bound needed by
    the raised-payload evaluator, after reversing the source-name map. -/
private def boundedParameterDecl : FunDecl Nat :=
  { name := "f"
    inline := false
    exported := false
    params := [("pair", .comb [.one, .one])]
    body := (.skip : Prog Nat)
    returnShape := .one }

example :
    ∀ name shape names,
      lookupInfo name
          ({ concreteRelContext with
              vars := panToCrepMakeVmap boundedParameterDecl.params
              maxVar := (compileParamVars boundedParameterDecl.params 0).2.2 } :
            CompileContext Nat).vars = some (shape, names) →
      ∀ slot ∈ names,
        slot ≤ ({ concreteRelContext with
          vars := panToCrepMakeVmap boundedParameterDecl.params
          maxVar := (compileParamVars boundedParameterDecl.params 0).2.2 } :
        CompileContext Nat).maxVar :=
  compileFunDecl_parameter_context_slots_bounded concreteRelContext
    boundedParameterDecl (by simp [boundedParameterDecl])

example :
    ∀ name shape names,
      lookupInfo name
          ({ concreteRelContext with
              vars := panToCrepMakeVmap boundedParameterDecl.params
              maxVar := Shape.shapeSize
                (.comb (boundedParameterDecl.params.map Prod.snd)) - 1 } :
            CompileContext Nat).vars = some (shape, names) →
      ∀ slot ∈ names,
        slot ≤ ({ concreteRelContext with
          vars := panToCrepMakeVmap boundedParameterDecl.params
          maxVar := Shape.shapeSize
            (.comb (boundedParameterDecl.params.map Prod.snd)) - 1 } :
        CompileContext Nat).maxVar :=
  compileFunDeclSource_parameter_context_slots_bounded concreteRelContext
    boundedParameterDecl (by simp [boundedParameterDecl])

/-! Cake's `eval_var_cexp_present_ctxt` (`pan_to_crepProofScript.sml:693`):
    every variable in a compiled expression is a slot bound in the compile
    context.  Flapjack's companion of `compileExp_vars_bounded`. -/
#check @Flapjack.compileExp_vars_present

/-! Cake's `eval_map_var_cexp_present_ctxt` list companion (`pan_to_crepProofScript.sml:1077`). -/
#check @Flapjack.compileExpList_vars_present

end Flapjack.Test.PanValuePcControlSafety
