import Flapjack.CrepeRuntimeGlobalCorrectness

namespace Flapjack

def globalLoadRuntimeState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun address => if address == 200 then some 42 else none
    functions := []
    memory := fun _ => none
    memaddrs := fun _ => true
    shMemaddrs := fun _ => true
    byteAlign := id
    clock := 10
    bigEndian := false
    ffi := ()
    baseAddress := 0
    topAddress := 100 }

def globalLoadRuntimeHandler : CrepRuntimeFfiHandler Nat Unit Unit :=
  fun _ state => .returned state

theorem crepRuntimeToLoop_loadGlob_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      globalLoadRuntimeState (.assign 5 (.loadGlob 200))).map
        (fun result => result.2.locals 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeStateForGlobals globalLoadRuntimeState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    globalLoadRuntimeState [] 5 200 42 (by simp [globalLoadRuntimeState])

theorem crepRuntimeToLoop_loadGlob_failure_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 2
      { globalLoadRuntimeState with globals := fun _ => none }
      (.assign 5 (.loadGlob 200))).bind
        (crepRuntimeLocalProjection 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3
      (loopStateOfCrepRuntimeStateForGlobals
        { globalLoadRuntimeState with globals := fun _ => none })
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  exact crepRuntimeToLoop_loadGlob_assign_failure_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } [] 5 200

theorem crepRuntimeToLoop_storeGlob_loadGlob_sequence_regression :
    (evalCrepRuntimeResult globalLoadRuntimeHandler (fun _ _ => none) 3
      { globalLoadRuntimeState with globals := fun _ => none }
      (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200)))).map
        (fun result => result.2.globals 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4
      (loopStateOfCrepRuntimeStateForGlobals
        { globalLoadRuntimeState with globals := fun _ => none })
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200))))).map
        (fun result => (loopResultState result).globals 200) := by
  exact crepRuntimeToLoop_storeGlob_loadGlob_sequence_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] globalLoadRuntimeHandler (fun _ _ => none) 1
    { globalLoadRuntimeState with globals := fun _ => none } 5 200 42

end Flapjack
