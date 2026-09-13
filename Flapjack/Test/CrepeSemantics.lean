import Flapjack.CrepeSemantics
import Flapjack.CrepeCorrectness
import Flapjack.CrepeRuntime
import Flapjack.Test.CrepCalls
import Flapjack.Test.OriginalPancakeProbes

namespace Flapjack

open Flapjack.Test.OriginalPancakeProbes

/-! Small executable witnesses for every control-result constructor in the
    full Crepe evaluator. These are deliberately word-polymorphic in the
    implementation, while the regression uses Nat to keep reduction fast. -/

def crepeSemanticsState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

/-! CakeML crepSem's set_var_def (crepSemScript.sml:55-57) updates exactly
    one local in the finite-map state and leaves every other local unchanged.
    updateCrepLocal is exercised at both the updated and untouched keys here. -/
def crepeSetVarLocals : Nat → Option Nat :=
  updateCrepLocal (fun name => if name == 2 then some 7 else none) 2 11

/- The source probe is the original Pancake redeclaration program.  Its
   Cake-derived RISC-V output is pinned in `setVar`; the two equations below
   check the corresponding `set_var_def` state transition in the Lean port. -/
#guard setVar.source =
  "fun 1 main() { var 1 x = 7; var 1 x = 11; return x; }"
#guard setVar.cakeByteCount == 1012

def crepeSetGlobals : Nat → Option Nat :=
  updateMemory (fun name => if name == 7 then some 3 else none) 7 11

/- CakeML crepSem's set_globals_def (crepSemScript.sml:61-63) updates one
   global binding.  The matching original Pancake global-initializer probe is
   checked in as `set_globals.pnk` and its generated output is pinned in
   `OriginalPancakeProbes.setGlobals`. -/
#guard setGlobals.source = "var 1 g = 7; fun 1 main() { return g; }"
#guard setGlobals.cakeByteCount == 1048

example : crepeSetGlobals 7 = some 11 := by
  decide

example : crepeSetGlobals 8 = none := by
  decide

def crepeUpdLocals : Option (Nat → Option Nat) :=
  assignCrepValues (fun _ => none) [1, 2] [7, 8]

/- CakeML crepSem's upd_locals_def (crepSemScript.sml:66-68) starts from an
   empty local map and installs the argument bindings.  The original Pancake
   call probe is `upd_locals.pnk`; its complete Cake output is pinned in
   `OriginalPancakeProbes.updLocals`. -/
#guard updLocals.source =
  "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }"
#guard updLocals.cakeByteCount == 1016

example :
    crepeUpdLocals.map (fun locals => (locals 1, locals 2)) =
      some (some 7, some 8) := by
  decide

example : crepeUpdLocals.map (fun locals => locals 3) = some none := by
  decide

def crepeEmptyLocals : Nat → Option Nat := fun _ => none

/- CakeML crepSem's empty_locals_def (crepSemScript.sml:71) clears the local
   map before evaluating a zero-argument callee.  The matching original probe
   and its complete generated-output hash are pinned in `emptyLocals`. -/
#guard emptyLocals.source =
  "fun 1 zero() { return 7; } fun 1 main() { return zero(); }"
#guard emptyLocals.cakeByteCount == 1016

example : crepeEmptyLocals 1 = none := by
  rfl

example : crepeEmptyLocals 2 = none := by
  rfl

def crepeLookupFunctions : List (CompiledFunction Nat) :=
  [{ name := "id", params := [1],
     body := .return [.var 1], returnShape := .one }]

def crepeLookupValid : Option (CrepProg Nat × (Nat → Option Nat)) :=
  lookupCrepCode "id" [7] crepeLookupFunctions

def crepeLookupDuplicateFunctions : List (CompiledFunction Nat) :=
  [{ name := "duplicate", params := [1, 1],
     body := .return [.var 1], returnShape := .one }]

/- CakeML crepSem's lookup_code_def (crepSemScript.sml:76-84) rejects missing
   names, arity mismatches, and duplicate formal names, and otherwise returns
   the body with a fresh local map made from the parameter/value zip.  The
   original call probe is `lookup_code.pnk`; its complete Cake output is
   pinned in `OriginalPancakeProbes.lookupCode`. -/
#guard lookupCode.source =
  "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }"
#guard lookupCode.cakeByteCount == 1016

example : crepeLookupValid.map (fun result => result.2 1) = some (some 7) := by
  decide

example : lookupCrepCode "id" [] crepeLookupFunctions = none := by
  decide

example : lookupCrepCode "duplicate" [7, 8]
    crepeLookupDuplicateFunctions = none := by
  decide

example : lookupCrepCode "missing" [7] crepeLookupFunctions = none := by
  decide

/- CakeML crepSem's crep_op_def (crepSemScript.sml:85-88) handles exactly a
   two-word multiplication and rejects every other operand shape.  The
   original source probe is `crep_op.pnk`; its complete Cake output is pinned
   in `OriginalPancakeProbes.crepOp`. -/
#guard crepOp.source = "fun 1 main() { return 6 * 7; }"
#guard crepOp.cakeByteCount == 1012

example : evalCrepOp .mul [6, 7] = some 42 := by
  decide

example : evalCrepOp .mul [6] = none := by
  decide

example : evalCrepOp .mul [6, 7, 8] = none := by
  decide

/- CakeML crepSem's dec_clock_def (crepSemScript.sml:145-148) decrements the
   clock with saturating natural subtraction and preserves every other state
   field.  The original `tick` probe is pinned in `OriginalPancakeProbes.decClock`. -/
#guard decClock.source = "fun 1 main() { tick; return 7; }"
#guard decClock.cakeByteCount == 1012

example : crepeSetVarLocals 2 = some 11 := by
  decide

example : crepeSetVarLocals 3 = none := by
  decide

def crepeSemanticsPrimitive : CrepPrimitiveHandler Nat
  | .addCarry, [left, right, carry] => some [left + right + carry, 0]
  | _, _ => none

def crepeSemanticsFfi : CrepFfiHandler Nat :=
  noCrepFfi Nat

def crepeSemanticsFfiHandler : CrepFfiHandler Nat :=
  fun function configuration configurationLength array arrayLength state =>
    if function == "sum" then
      some (.returned { state with
        memory := updateMemory state.memory 99
          (configuration + configurationLength + array + arrayLength) })
    else none

def crepeSemanticsFinalEvent : FfiFinalEvent :=
  { name := .extCall "halt"
    configuration := []
    bytes := []
    outcome := .failed }

def crepeSemanticsFinalHandler : CrepFfiHandler Nat :=
  fun _ _ _ _ _ _ => some (.final crepeSemanticsFinalEvent)

def crepeSemanticsFinalState : CrepState Nat :=
  { locals := fun name =>
      match name with
      | 1 | 2 | 3 | 4 => some 0
      | _ => none
    memory := fun _ => none }

def crepeSemanticsSharedMem : CrepSharedMemHandler Nat :=
  defaultCrepSharedMemHandler

def crepeSemanticsFunctions : List (CompiledFunction Nat) :=
  [{ name := "inc"
     params := [0]
     body := .return [.op .add [.var 0, .const 1]]
     returnShape := .one }]

def crepeSemanticsCall : CrepProg Nat :=
  .seq
    (.dec 1 (.const 41)
      (.call (some ([2], none)) "inc" [.var 1]))
    (.return [.var 2])

def crepeSemanticsLoop : CrepProg Nat :=
  .seq
    (.assign 0 (.const 3))
    (.seq
      (.while (.var 0)
        (.seq
          (.assign 0 (.op .sub [.var 0, .const 1]))
          (.ite (.cmp .equal (.var 0) (.const 0)) (.break 0) .skip)))
      (.return [.var 0]))

def crepeSemanticsHandlerFunctions : List (CompiledFunction Nat) :=
  [{ name := "raise"
     params := []
     body := .raise 7
     returnShape := .one }]

def crepeSemanticsHandlerCall : CrepProg Nat :=
  .call (some ([], some (7, .return [.const 9]))) "raise" []

def crepeSemanticsMemory : CrepProg Nat :=
  .seq
    (.store (.const 10) (.const 7))
    (.seq
      (.shMem .load 0 (.const 10))
      (.return [.var 0]))

def crepeSemanticsPrimitiveProgram : CrepProg Nat :=
  .seq
    (.assign 1 (.const 1))
    (.seq
      (.assign 2 (.const 2))
      (.seq
        (.assign 3 (.const 0))
        (.seq
          (.primitive [4, 5] .addCarry [1, 2, 3])
          (.return [.var 4]))))

def crepeSemanticsFfiProgram : CrepProg Nat :=
  crepNestedSeq
    [.assign 1 (.const 10), .assign 2 (.const 1),
     .assign 3 (.const 20), .assign 4 (.const 2),
     .extCall "sum" 1 2 3 4, .return [.load (.const 99)]]

def crepeFfiContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

def crepeRuntimeState : CrepRuntimeState Nat Unit :=
  { locals := fun name =>
      match name with
      | 1 => some 10
      | 2 => some 1
      | 3 => some 20
      | 4 => some 2
      | 5 => some 0
      | _ => none
    globals := fun _ => none
    functions := []
    memory := fun address =>
      if address == 10 then some 7
      else if address == 20 then some 20
      else if address == 21 then some 21
      else none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 1
    ffiContext := natCrepRuntimeFfiContext
    clock := 10
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

example : (decCrepClock { crepeRuntimeState with clock := 10 }).clock = 9 := by
  rfl

example : (decCrepClock { crepeRuntimeState with clock := 0 }).clock = 0 := by
  rfl

def crepeRuntimeFinalHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .extCall _ _ _ => .final "halt"
    | .sharedMem _ _ _ _ => .returned state []

def crepeRuntimeSharedHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .sharedMem .load _ address _ =>
        match state.memory address with
        | some value =>
            .returned state [state.ffiContext.wordToByte value]
        | none => .returned state []
    | .sharedMem _ _ _ _ => .returned state []
    | .extCall _ _ _ => .returned state []

def crepeRuntimeByteReturnHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .extCall _ _ _ => .returned state [99, 100]
    | .sharedMem _ _ _ _ => .returned state []

def crepeRuntimeFfiStatefulHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .extCall function configuration array =>
        match callFfi state.ffi (.extCall function) configuration array with
        | .returned ffi bytes => .returned { state with ffi := ffi } bytes
        | .final _ => .final "halt"
    | .sharedMem _ _ _ _ => .returned state []

def crepeRuntimeShortOracle : FfiOracle Unit :=
  fun _ state _ _ => .returned state []

def crepeRuntimeShortState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    ffi := { crepeRuntimeState.ffi with oracle := crepeRuntimeShortOracle } }

theorem crepe_full_call_semantics :
    evalCrepFullResult crepeSemanticsFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsCall =
      some [42] := by
  decide +kernel

theorem crepe_full_loop_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 50 crepeSemanticsState crepeSemanticsLoop =
      some [0] := by
  decide +kernel

theorem crepe_full_handler_semantics :
    evalCrepFullResult crepeSemanticsHandlerFunctions
      crepeSemanticsPrimitive crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsHandlerCall =
      some [9] := by
  decide +kernel

theorem crepe_full_memory_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsMemory =
      some [7] := by
  decide +kernel

theorem crepe_full_primitive_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfi crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsPrimitiveProgram =
      some [3] := by
  decide +kernel

theorem crepe_full_ffi_semantics :
    evalCrepFullResult [] crepeSemanticsPrimitive
      crepeSemanticsFfiHandler crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState crepeSemanticsFfiProgram =
      some [33] := by
  simp [evalCrepFullResult, evalCrepFullProg, evalCrepFullExp,
    evalCrepFullExps, crepeSemanticsFfiHandler, crepeSemanticsFfiProgram,
    crepNestedSeq, updateCrepLocal, updateMemory]

theorem crepe_full_ffi_final_semantics :
    evalCrepFullProg [] crepeSemanticsPrimitive
      crepeSemanticsFinalHandler crepeSemanticsSharedMem
      0 100 30 crepeSemanticsFinalState
      (.extCall "halt" 1 2 3 4) =
      some (.finalFfi crepeSemanticsFinalState crepeSemanticsFinalEvent) := by
  simp [evalCrepFullProg, crepeSemanticsFinalHandler,
    crepeSemanticsFinalState, crepeSemanticsFinalEvent]

theorem crepe_full_ffi_lowering_noop :
    evalCrepFullProgState [] crepeSemanticsPrimitive
      (fun _ _ _ _ _ state => some (.returned state)) crepeSemanticsSharedMem
      0 100 30 crepeSemanticsState
      (compileProg crepeFfiContext
        (.extCall "noop" (.const 10) (.const 1) (.const 20) (.const 2))) =
      some (.normal crepeSemanticsState) := by
  exact compile_full_extCall_const_noop_correct
    crepeFfiContext crepeSemanticsState
    crepeSemanticsPrimitive crepeSemanticsSharedMem
    0 100 10 1 20 2 "noop"

theorem crepe_runtime_extCall_final :
    (crepRuntimeExtCall crepeRuntimeFinalHandler crepeRuntimeState
      "host" 1 2 3 4).1 = .finalFfi "halt" := by
  simp [crepRuntimeExtCall, crepRuntimeExtCallValues, crepeRuntimeState,
    natCrepRuntimeFfiContext, natCrepRuntimeMemoryModel,
    crepeRuntimeFinalHandler, crepRuntimeReadBytes, crepRuntimeLoadByte]

theorem crepe_runtime_empty_extCall_is_identity :
    (crepRuntimeExtCall crepeRuntimeFinalHandler crepeRuntimeState
      "" 1 2 3 4).1 = .normal := by
    simp [crepRuntimeExtCall, crepRuntimeExtCallValues, crepeRuntimeState,
    natCrepRuntimeFfiContext, natCrepRuntimeMemoryModel,
    crepRuntimeReadBytes, crepRuntimeLoadByte,
    crepRuntimeWriteBytes, crepRuntimeStoreByte, updateMemory]

theorem crepe_runtime_extCall_return_writes_bytes :
    let result := crepRuntimeExtCall crepeRuntimeByteReturnHandler
      crepeRuntimeState "host" 1 2 3 4
    result.1 = .normal ∧ result.2.memory 20 = some 99 ∧
      result.2.memory 21 = some 100 := by
  simp [crepRuntimeExtCall, crepRuntimeExtCallValues, crepeRuntimeState,
    natCrepRuntimeFfiContext, natCrepRuntimeMemoryModel,
    crepeRuntimeByteReturnHandler, crepRuntimeReadBytes, crepRuntimeLoadByte,
    crepRuntimeWriteBytes, crepRuntimeStoreByte, updateMemory]

theorem crepe_runtime_ffi_state_transition :
    let result := crepRuntimeExtCall crepeRuntimeFfiStatefulHandler
      crepeRuntimeState "host" 1 2 3 4
    result.1 = .normal ∧ result.2.ffi.ioEvents.length = 1 := by
  simp [crepRuntimeExtCall, crepRuntimeExtCallValues,
    crepeRuntimeFfiStatefulHandler, crepeRuntimeState,
    natCrepRuntimeFfiState, natCrepRuntimeFfiOracle,
    natCrepRuntimeFfiContext, natCrepRuntimeMemoryModel,
    crepRuntimeReadBytes, crepRuntimeLoadByte, crepRuntimeWriteBytes,
    crepRuntimeStoreByte, updateMemory, callFfi]

theorem crepe_runtime_ffi_length_mismatch_is_final :
    let result := crepRuntimeExtCall crepeRuntimeFfiStatefulHandler
      crepeRuntimeShortState "host" 1 2 3 4
    result.1 = .finalFfi "halt" ∧ result.2.ffi.ioEvents.length = 0 := by
  simp [crepRuntimeExtCall, crepRuntimeExtCallValues,
    crepeRuntimeFfiStatefulHandler, crepeRuntimeShortState,
    crepeRuntimeShortOracle, crepeRuntimeState,
    natCrepRuntimeFfiState,
    natCrepRuntimeFfiContext, natCrepRuntimeMemoryModel,
    crepRuntimeReadBytes, crepRuntimeLoadByte, callFfi]

theorem crepe_runtime_shared_load :
    (crepRuntimeSharedMem crepeRuntimeSharedHandler crepeRuntimeState
      .load 5 10).1 = .normal ∧
    (crepRuntimeSharedMem crepeRuntimeSharedHandler crepeRuntimeState
      .load 5 10).2.locals 5 = some 7 := by
  decide

theorem crepe_runtime_shared_address_error :
    (crepRuntimeSharedMem crepeRuntimeSharedHandler
      { crepeRuntimeState with shMemaddrs := fun _ => false }
      .load 5 10).1 = .error := by
  decide

def crepeRuntimeReturnProgram : CrepProg Nat :=
  .seq (.assign 5 (.const 3)) (.return [.var 5])

theorem crepe_runtime_full_return :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeState
      crepeRuntimeReturnProgram).map Prod.fst =
      some (.returned [3]) := by
  decide +kernel

theorem crepe_runtime_full_final_ffi :
    (evalCrepRuntimeResult crepeRuntimeFinalHandler
      crepeSemanticsPrimitive 20 crepeRuntimeState
      (.extCall "host" 1 2 3 4)).map Prod.fst =
      some (.finalFfi "halt") := by
  decide +kernel

theorem crepe_runtime_tick_timeout :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2 { crepeRuntimeState with clock := 0 }
      .tick).map Prod.fst =
      some (.timeout : CrepRuntimeResult Nat String) := by
  decide +kernel

def crepeRuntimeWhileTimeoutProgram : CrepProg Nat :=
  .while (.const 1) .skip

theorem crepe_runtime_while_zero_timeout_clears_locals :
    let result := evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 { crepeRuntimeState with clock := 0 }
      crepeRuntimeWhileTimeoutProgram
    result.map Prod.fst = some (.timeout : CrepRuntimeResult Nat String) ∧
      result.map (fun step => step.2.locals 5) = some none := by
  decide +kernel

def crepeRuntimeEndianHandler : CrepRuntimeFfiHandler Nat Unit String :=
  fun request state =>
    match request with
    | .sharedMem .load _ _ _ => .returned state [11, 22]
    | .sharedMem _ _ _ _ => .returned state []
    | .extCall _ _ _ => .returned state []

def crepeRuntimeEndianState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    ffiContext :=
      { natCrepRuntimeFfiContext with
        bigEndian := true
        wordOfBytes := fun bigEndian bytes =>
          if bigEndian then
            match bytes with
            | _ :: value :: _ => value.toNat
            | _ => 0
          else
            match bytes with
            | value :: _ => value.toNat
            | [] => 0 } }

theorem crepe_runtime_shared_load_uses_source_little_endian :
    (crepRuntimeSharedMem crepeRuntimeEndianHandler
      crepeRuntimeEndianState .load 5 10).2.locals 5 = some 11 := by
  decide

/- CakeML `crepSemScript.sml:333` returns `TimeOut` with `empty_locals s`.
   Keep the post-state clause observable instead of checking only the result. -/
theorem crepe_runtime_tick_timeout_clears_locals :
    ((evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2
      { crepeRuntimeState with clock := 0 }
      .tick).map Prod.snd).map (fun state => state.locals 1) =
      some none := by
  decide +kernel

theorem crepe_runtime_memory_domain_error :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2
      { crepeRuntimeState with memaddrs := fun _ => false }
      (.store (.const 10) (.const 7))).map Prod.fst =
      some (.error : CrepRuntimeResult Nat String) := by
  decide +kernel

def crepeRuntimeCallState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    functions :=
      [{ name := "inc"
         params := [0]
         body := .return [.op .add [.var 0, .const 1]]
         returnShape := .one }] }

theorem crepe_runtime_call_result :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeCallState
      (.call (some ([5], none)) "inc" [.const 41])).map
        (fun result => (result.1, result.2.locals 5)) =
      some (.normal, some 42) := by
  decide +kernel

theorem crepe_runtime_nary_add :
    evalCrepRuntimeExp crepeRuntimeState
      (.op .add [.const 1, .const 2, .const 3]) = some 6 := by
  simp [evalCrepRuntimeExp, crepeRuntimeState, natCrepRuntimeMemoryModel]

def crepeRuntimeDuplicateParameterState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    functions :=
      [{ name := "bad"
         params := [0, 0]
         body := .return [.const 0]
         returnShape := .one }] }

theorem crepe_runtime_call_rejects_duplicate_parameters :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeDuplicateParameterState
      (.call none "bad" [.const 1, .const 2])).map Prod.fst =
      some (.error : CrepRuntimeResult Nat String) := by
  decide +kernel

def crepeRuntimeFallthroughState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    functions :=
      [{ name := "fallthrough"
         params := [0]
         body := .skip
         returnShape := .one }] }

theorem crepe_runtime_call_fallthrough_is_error :
    (evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 20 crepeRuntimeFallthroughState
      (.call none "fallthrough" [.const 41])).map
        (fun result => (result.1, result.2.locals 0)) =
      some (.error, some 41) := by
  decide +kernel

def crepeCallFullState : CrepState (RiscV.Word 64) :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepeCallFullPrimitive : CrepPrimitiveHandler (RiscV.Word 64) :=
  fun _ _ => none

def crepeCallFullFfi : CrepFfiHandler (RiscV.Word 64) :=
  noCrepFfi _

def crepeCallFullSharedMem : CrepSharedMemHandler (RiscV.Word 64) :=
  defaultCrepSharedMemHandler

def crepeCallFullValues :
    Option (List (RiscV.Word 64)) :=
  do
    let (_, main) ← lookupCompiledFunction "main" crepCallFunctions
    let result ← evalCrepFullProg crepCallFunctions
      crepeCallFullPrimitive crepeCallFullFfi crepeCallFullSharedMem
      0 (BitVec.ofNat 64 100) 30 crepeCallFullState main
    pure (match result with
      | .returned _ values => values
      | .normal _ => []
      | .raised _ _ | .broke _ _ | .continued _ _ | .finalFfi _ _ => [])

#guard
    crepeCallFullValues = some [BitVec.ofNat 64 41]

#guard
    crepeCallFullValues =
      (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
        pipelineCallSourceMain).map (fun result => result.2)

end Flapjack
