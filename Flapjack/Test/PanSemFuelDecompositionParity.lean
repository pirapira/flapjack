/-
  Kernel-checked regression for the canonical source-evaluator fuel
  decomposition (bead flapjack-pxn.18.4.3.74.1): the Call/DecCall callee,
  handler and continuation programs are evaluated at a fuel derived from
  `panSemCodeEvaluateFuel`, not supplied as an `hsourceFuel` premise.
-/
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

namespace Flapjack.Test.PanSemFuelDecompositionParity

open Flapjack

private abbrev W64 := RiscV.Word 64

/-- A one-entry source code map whose body is `Skip`. -/
private def sampleCode : PanSemCodeMap Nat :=
  [("f", ([("p", Shape.one)], Prog.skip, Shape.one))]

/-- A source state with clock 5 and the sample code. -/
private def sampleState : PanSemState Nat (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := sampleCode
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

/-- The stored body's fuel is bounded by the code body fuel. -/
example : panSemProgFuel (Prog.skip : Prog Nat) ≤ panSemCodeBodyFuel sampleCode :=
  panSemProgFuel_le_codeBodyFuel_of_mem sampleCode (by
    rw [sampleCode]
    exact List.mem_singleton_self _)

/-- A `Skip` body costs at least one. -/
example : 1 ≤ panSemProgFuel (Prog.skip : Prog Nat) := panSemProgFuel_pos _

/-- The callee body runs at canonical Call fuel minus two. -/
example :
    panSemCodeEvaluateFuel
        { sampleState with clock := decPanClock sampleState.clock, locals := fun _ => none }
        (Prog.skip : Prog Nat)
      ≤ panSemCodeEvaluateFuel sampleState (.call none "f" []) - 2 :=
  panSemCodeEvaluateFuel_call_callee_le sampleState none "f" [] Prog.skip
    [("p", Shape.one)] Shape.one (fun _ => none) (by decide) (by
      rw [sampleState]
      exact List.mem_singleton_self _)

/-- A handler body carried in the Call metadata runs at canonical Call fuel
    minus two. -/
example :
    panSemCodeEvaluateFuel
        { sampleState with clock := decPanClock sampleState.clock, locals := fun _ => none }
        (Prog.skip : Prog Nat)
      ≤ panSemCodeEvaluateFuel sampleState
          (.call (some (none, some ("e", "h", Prog.skip))) "f" []) - 2 :=
  panSemCodeEvaluateFuel_call_handler_le sampleState
    (some (none, some ("e", "h", Prog.skip))) "f" [] Prog.skip "e" "h"
    (fun _ => none) (by decide) rfl

/-- A `DecCall` continuation body runs at canonical DecCall fuel minus one. -/
example :
    panSemCodeEvaluateFuel
        { sampleState with clock := decPanClock sampleState.clock, locals := fun _ => none }
        (Prog.skip : Prog Nat)
      ≤ panSemCodeEvaluateFuel sampleState
          (.decCall "r" Shape.one "f" [] Prog.skip) - 1 := by
  refine panSemCodeEvaluateFuel_decCall_body_le sampleState "r" Shape.one "f" []
    Prog.skip Prog.skip (fun _ => none) (by decide) ?_
  simp only [panSemProgFuel]
  omega

/-- The body selected from the nonempty state-owned code map gets a DecCall
    callee budget derived from the enclosing canonical fuel. -/
example :
    panSemCodeEvaluateFuel
        { sampleState with clock := decPanClock sampleState.clock, locals := fun _ => none }
        (Prog.skip : Prog Nat)
      ≤ panSemCodeEvaluateFuel sampleState
          (.decCall "r" Shape.one "f" [] (Prog.skip : Prog Nat)) - 2 := by
  apply panSemCodeEvaluateFuel_decCall_callee_le sampleState "r" Shape.one "f"
    [] Prog.skip Prog.skip (fun _ => none) [("p", Shape.one)] Shape.one
    (by decide) ?_
  simp [sampleState, sampleCode, panSemCodeLookup, lookupInfo]

/-- A 64-bit source state, to exercise the Call dispatch decomposition with the
    production RV64 context. -/
private def sampleRiscvState : PanSemState W64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := [("f", ([("p", Shape.one)], (Prog.skip : Prog W64), Shape.one))]
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

/-- The canonical-fuel Call dispatches to the state-owned call clause at
    canonical fuel minus one. -/
example :
    evalPanValueFfiClockCodeProg statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState (.call none "f" ([] : List (Exp W64))))
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock
        (.call none "f" ([] : List (Exp W64))) none none none =
      evalPanValueFfiClockCodeCall statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState (.call none "f" ([] : List (Exp W64))) - 1)
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock none "f" ([] : List (Exp W64))
        none none none :=
  panSemCodeEvaluateFuel_call_delegates statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) sampleRiscvState none "f" []
    none none none

/-- Numeric sanity check of the canonical fuel formula at clock 5 with a `Skip`
    code body: `(5 + 1) * (max 1 1 + 1) + 1 = 13`. -/
example : panSemCodeEvaluateFuel sampleState (.call none "f" []) = 13 := by decide

/-- The canonical Call fuel is at least two, so the body budget never
    underflows at the two dispatch steps. -/
example : 2 ≤ panSemCodeEvaluateFuel sampleState (.call none "f" []) :=
  panSemCodeEvaluateFuel_call_two_le sampleState none "f" []

/-- The state-owned call-clause fuel is one more than the body budget
    `canonical - 2`, so the recursive callee/handler bodies run exactly there. -/
example : panSemCodeEvaluateFuel sampleState (.call none "f" []) - 1 =
    (panSemCodeEvaluateFuel sampleState (.call none "f" []) - 2) + 1 :=
  panSemCodeEvaluateFuel_call_sub_one_eq sampleState none "f" []

/-- At canonical fuel, `DecCall` dispatches to the new state-code helper,
    retaining the source code map, clock, and caller state. -/
example :
    evalPanValueFfiClockCodeProg statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState
          (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip))
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock
        (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip) none none none =
      evalPanValueFfiClockCodeDecCall statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState
          (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip) - 1)
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock "r" Shape.one "f"
        ([] : List (Exp W64)) Prog.skip none none none :=
  panSemCodeEvaluateFuel_decCall_delegates statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) sampleRiscvState
    "r" Shape.one "f" [] Prog.skip none none none

/-- The canonical DecCall budget leaves room for the code-map helper and its
    callee body. -/
example : 2 ≤ panSemCodeEvaluateFuel sampleState
    (.decCall "r" Shape.one "f" [] Prog.skip) :=
  panSemCodeEvaluateFuel_decCall_two_le sampleState "r" Shape.one "f" [] Prog.skip

example : panSemCodeEvaluateFuel sampleState
      (.decCall "r" Shape.one "f" [] Prog.skip) - 1 =
    (panSemCodeEvaluateFuel sampleState
      (.decCall "r" Shape.one "f" [] Prog.skip) - 2) + 1 :=
  panSemCodeEvaluateFuel_decCall_sub_one_eq sampleState "r" Shape.one "f" [] Prog.skip

/-- The DecCall branch decomposition exposes the helper's successor budget,
    matching the actual code-bearing helper call. -/
example :
    evalPanValueFfiClockCodeProg statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState
          (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip))
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock
        (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip) none none none =
      evalPanValueFfiClockCodeDecCall statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        ((panSemCodeEvaluateFuel sampleRiscvState
          (.decCall "r" Shape.one "f" ([] : List (Exp W64)) Prog.skip) - 2) + 1)
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock "r" Shape.one "f"
        ([] : List (Exp W64)) Prog.skip none none none :=
  panSemCodeEvaluateFuel_decCall_decomposition statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) sampleRiscvState
    "r" Shape.one "f" [] Prog.skip none none none

/-- The exact `Call` branch decomposition: canonical fuel dispatches to the
    state-owned call clause at the syntactically-successor fuel
    `(canonical - 2) + 1`, exposing the callee body recursion at `canonical - 2`. -/
example :
    evalPanValueFfiClockCodeProg statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        (panSemCodeEvaluateFuel sampleRiscvState (.call none "f" ([] : List (Exp W64))))
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock
        (.call none "f" ([] : List (Exp W64))) none none none =
      evalPanValueFfiClockCodeCall statefulTestContext statefulTestPrimitive
        statefulTestHandler sampleRiscvState.structs sampleRiscvState.code
        sampleRiscvState.exceptionShapes sampleRiscvState.baseAddress
        sampleRiscvState.topAddress (BitVec.ofNat 64 8)
        ((panSemCodeEvaluateFuel sampleRiscvState (.call none "f" ([] : List (Exp W64))) - 2) + 1)
        sampleRiscvState.locals sampleRiscvState.globals sampleRiscvState.memory
        sampleRiscvState.ffi sampleRiscvState.clock none "f" ([] : List (Exp W64))
        none none none :=
  panSemCodeEvaluateFuel_call_decomposition statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) sampleRiscvState none "f" []
    none none none

def runChecks : IO Bool := do
  IO.println "PASS PanSem fuel decomposition: stored body bounded by code body fuel"
  IO.println "PASS PanSem fuel decomposition: canonical Call callee fuel = canonical - 2"
  IO.println "PASS PanSem fuel decomposition: canonical Call handler fuel = canonical - 2"
  IO.println "PASS PanSem fuel decomposition: canonical DecCall continuation fuel = canonical - 1"
  IO.println "PASS PanSem fuel decomposition: state-owned DecCall callee fuel = canonical - 2"
  IO.println "PASS PanSem fuel decomposition: canonical DecCall dispatches to the code-map helper"
  IO.println "PASS PanSem fuel decomposition: canonical DecCall helper fuel = canonical - 1"
  IO.println "PASS PanSem fuel decomposition: canonical DecCall decomposition preserves helper state"
  IO.println "PASS PanSem fuel decomposition: canonical Call dispatches at canonical - 1"
  IO.println "PASS PanSem fuel decomposition: canonical Call decomposition exposes body at canonical - 2"
  pure true

end Flapjack.Test.PanSemFuelDecompositionParity
