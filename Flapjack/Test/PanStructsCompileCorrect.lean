import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Test.PanValueFfiSemantics

/-! Regression cases paired with
`scripts/hol-probes/pan_structs_compile_correct_probe.out`. -/

namespace Flapjack.Test

open Flapjack

example :
    panStructConvertValue
      (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) =
        .rStruct [.word 3, .word 5] := by
  simp [panStructConvertValue, panStructConvertFieldValues]

example (context : StructPassContext) :
    structCompileProg context (.skip : Prog Nat) = .skip := by
  exact panStructCompileSkip_eq_skip context

private abbrev Word64 := Flapjack.RiscV.Word 64

def finiteMapRuntime : PanSemState Word64 (FfiState Unit) where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := []
  exceptionShapes := fun _ => none
  memory := fun _ => none
  memaddrs := fun _ => false
  sharedMemaddrs := fun _ => false
  clock := 3
  be := false
  ffi := statefulTestFfiState
  baseAddress := BitVec.ofNat 64 0
  topAddress := BitVec.ofNat 64 100

def finiteMapContext : StructPassContext where
  structs := []
  locals := [("local", .one)]
  globals := [("global", .one)]

def finiteMapState : PanStructFiniteState Word64 (FfiState Unit) :=
  panStructFiniteStateFromMaps finiteMapRuntime
    [("local", .word (BitVec.ofNat 64 7))]
    [("global", .word (BitVec.ofNat 64 11))] [("E", .one)]
    [("f", ([], .skip, .one))]
    (by simp) (by simp) (by simp) (by simp)

def finiteMapStateAtClock (clock : Nat) :
    PanStructFiniteState Word64 (FfiState Unit) :=
  { finiteMapState with
    runtime := { finiteMapState.runtime with clock := clock } }

example : finiteMapState.runtime.locals "local" =
    some (.word (BitVec.ofNat 64 7)) := by
  rfl

example : finiteMapState.runtime.globals "global" =
    some (.word (BitVec.ofNat 64 11)) := by
  rfl

example : finiteMapState.runtime.exceptionShapes "E" = some .one := by
  rfl

example : finiteMapState.runtime.locals "local" =
    panPropsALookupEq "local" finiteMapState.locals := by
  exact finiteMapState.locals_lookup "local"

example : lookupInfo "f" finiteMapState.runtime.code =
    panPropsALookupEq "f" finiteMapState.runtime.code := by
  exact lookupInfo_eq_panPropsALookupEq "f" finiteMapState.runtime.code

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).locals =
      [("local", .word (BitVec.ofNat 64 7))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).globals =
      [("global", .word (BitVec.ofNat 64 11))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).exceptionShapes =
      [("E", .one)] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, structCompileShape, structCompileShapeWF]

example :
    lookupInfo "f" (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.code =
      some ([], .skip, .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertCode,
    structCompileShape, structCompileShapeWF, lookupInfo]

example :
    ((panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
        "local",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
        "global",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.exceptionShapes
        "E") =
      (some (.word (BitVec.ofNat 64 7)),
        some (.word (BitVec.ofNat 64 11)), some .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertValue,
    panPropsALookupEq, structCompileShape, structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.skip : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
          finiteMapState.runtime.memory finiteMapState.runtime.ffi),
          finiteMapState.runtime.clock), finiteMapState.runtime) := by
  exact (panStructSkipFiniteMapEvaluatorSupport finiteMapContext statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState).1

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8)
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime
        (structCompileProg finiteMapContext (.skip : Prog Word64)) =
      some ((.control (.normal
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.memory
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.ffi),
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.clock),
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime) := by
  exact (panStructSkipFiniteMapEvaluatorSupport finiteMapContext statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState).2

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8)
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime
        (structCompileProg finiteMapContext (.skip : Prog Word64)) =
      (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime
        (.skip : Prog Word64)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState finiteMapContext postState)) := by
  exact panStructFiniteMapSkipEvaluationProjection finiteMapContext
    statefulTestContext statefulTestPrimitive statefulTestHandler
    (BitVec.ofNat 64 8) finiteMapState

example : True := by
  have _hcase := panStructCompileCorrectSkipCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState
      (panSemEvaluateCodeStateWithPostState_skip statefulTestContext
        statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
        finiteMapState.runtime)
      rfl
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
        finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

private theorem finiteMapTickCaseRegression (clock : Nat) : True := by
  let state := finiteMapStateAtClock clock
  have _hcase := panStructCompileCorrectTickCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) state
      (by rfl)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, state, finiteMapStateAtClock, finiteMapState,
        panStructFiniteStateFromMaps, finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

example : True := finiteMapTickCaseRegression 0

example : True := finiteMapTickCaseRegression 3

/-! These four result/state assertions pair the checked-in HOL `TimeOut` and
`NONE` rows with the concrete production evaluator representation. At clock
zero both source and converted states time out and clear locals. At clock three
both continue with normal control and decrement to clock two, preserving
locals, globals, memory, and FFI state. -/

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.tick : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.ffi), 2),
        { finiteMapState.runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapState,
    panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 3)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.control (.normal
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.locals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.ffi), 2),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 3)).runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (finiteMapStateAtClock 0).runtime (.tick : Prog Word64) =
      some ((.timeout (fun _ => none) (finiteMapStateAtClock 0).runtime.globals
        (finiteMapStateAtClock 0).runtime.memory (finiteMapStateAtClock 0).runtime.ffi, 0),
        { (finiteMapStateAtClock 0).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapStateAtClock,
    finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 0)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.timeout (fun _ => none)
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.ffi, 0),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 0)).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

end Flapjack.Test
