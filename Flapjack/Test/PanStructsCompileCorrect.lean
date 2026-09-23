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
  locals := []
  globals := []

def finiteMapState : PanStructFiniteState Word64 (FfiState Unit) :=
  panStructFiniteStateFromMaps finiteMapRuntime
    [("local", .word (BitVec.ofNat 64 7))]
    [("global", .word (BitVec.ofNat 64 11))] [("E", .one)]
    [("f", ([], .skip, .one))]
    (by simp) (by simp) (by simp) (by simp)

example : finiteMapState.runtime.locals "local" =
    some (.word (BitVec.ofNat 64 7)) := by
  rfl

example : finiteMapState.runtime.globals "global" =
    some (.word (BitVec.ofNat 64 11)) := by
  rfl

example : finiteMapState.runtime.exceptionShapes "E" = some .one := by
  rfl

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
    lookupInfo, structCompileShape, structCompileShapeWF]

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

end Flapjack.Test
