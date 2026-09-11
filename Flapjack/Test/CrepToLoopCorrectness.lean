import Flapjack.CrepToLoopCorrectness

/-! Concrete regression for the Crepe-to-Loop FFI state correspondence. -/

namespace Flapjack

def crepLoopFfiState : CrepState Nat :=
  { locals := fun name =>
      if name == 1 then some 41
      else if name == 2 then some 0
      else if name == 3 then some 0
      else if name == 4 then some 0
      else none
    memory := fun _ => none }

def crepLoopFfi : CrepFfiHandler Nat :=
  fun _ configuration _ _ _ state =>
    some (.returned { state with
      locals := updateCrepLocal state.locals 9 (configuration + 1) })

def crepLoopFfiStateAfter : CrepState Nat :=
  { crepLoopFfiState with
    locals := updateCrepLocal crepLoopFfiState.locals 9 42 }

def crepLoopAssignState : CrepState Nat :=
  { locals := fun name => if name == 5 then some 1 else none
    memory := fun _ => none }

def crepSeqInitial : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepSeqMiddle : CrepState Nat :=
  { crepSeqInitial with
    locals := updateCrepLocal crepSeqInitial.locals 5 42 }

def crepSeqFinal : CrepState Nat :=
  { crepSeqMiddle with
    locals := updateCrepLocal crepSeqMiddle.locals 6 42 }

theorem crepToLoop_seq_normal_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 100 4 crepSeqInitial
        (.seq (.assign 5 (.const 42)) (.assign 6 (.var 5))) =
      some (.normal crepSeqFinal) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        4 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.seq (.assign 5 (.const 42)) (.assign 6 (.var 5)))) =
      some (.normal (loopStateOfCrepState crepSeqFinal)) := by
  have hupdate : ∀ (locals : Nat → Option Nat) (name value : Nat),
      updateLoopLocal locals name value = updateCrepLocal locals name value := by
    intro locals name value
    funext current
    simp [updateLoopLocal, updateCrepLocal]
  apply crepToLoop_seq_normal_compose
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ loopState => some loopState) (fun _ _ _ _ => none)
    0 100 2 crepSeqInitial crepSeqMiddle []
    (.assign 5 (.const 42)) (.assign 6 (.var 5))
    (.normal crepSeqFinal) (.normal (loopStateOfCrepState crepSeqFinal))
  all_goals simp [crepSeqInitial, crepSeqMiddle, crepSeqFinal,
    loopStateOfCrepState, updateCrepLocal, hupdate,
    evalCrepFullProg, evalCrepFullExp, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp]

def crepLoopLoadState : CrepState Nat :=
  { locals := fun name => if name == 5 then some 1 else none
    memory := fun address => if address == 100 then some 42 else none }

theorem crepToLoop_store_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.store (.const 200) (.const 42))).map
        (crepControlMemoryAt 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      6 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.store (.const 200) (.const 42)))).map
        (loopControlMemoryAt 200) := by
  exact crepToLoop_store_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopAssignState [] 200 42

theorem crepToLoop_assign_load32_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopLoadState
      (.assign 5 (.load32 (.const 100)))).map (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopLoadState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.load32 (.const 100))))).map (loopControlLocal 5) := by
  apply crepToLoop_assign_load32_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopLoadState [] 5 100 42
  simp [crepLoopLoadState]

theorem crepToLoop_assign_loadByte_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopLoadState
      (.assign 5 (.loadByte (.const 100)))).map (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopLoadState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadByte (.const 100))))).map (loopControlLocal 5) := by
  apply crepToLoop_assign_loadByte_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopLoadState [] 5 100 42
  simp [crepLoopLoadState]

theorem crepToLoop_assign_var_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.assign 5 (.var 6))).map (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.var 6)))).map (loopControlLocal 5) := by
  exact crepToLoop_assign_var_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopAssignState [] 5 6

theorem crepToLoop_assign_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.assign 5 (.const 42))).map (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.const 42)))).map (loopControlLocal 5) := by
  exact crepToLoop_assign_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopAssignState [] 5 42

theorem crepToLoop_extCall_simulation_regression :
    evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 4 crepLoopFfiState
        (.extCall "inc" 1 2 3 4) =
        some (.normal crepLoopFfiStateAfter) ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFfi) 4
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
          [9] (.extCall "inc" 1 2 3 4)) =
        some (.normal (loopStateOfCrepState crepLoopFfiStateAfter)) := by
  apply crepToLoop_extCall_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState crepLoopFfiStateAfter [9] "inc" 1 2 3 4
    41 0 0 0
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfi, crepLoopFfiState, crepLoopFfiStateAfter]

def crepLoopUnavailableFfi : CrepFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

theorem crepToLoop_extCall_failure_regression :
    evalCrepFullProg [] (fun _ _ => none) crepLoopUnavailableFfi
        (fun _ _ _ _ => none) 0 100 4 crepLoopFfiState
        (.extCall "missing" 1 2 3 4) = none ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopUnavailableFfi) 4
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.extCall "missing" 1 2 3 4)) = none := by
  apply crepToLoop_extCall_failure_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopUnavailableFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState [9] "missing" 1 2 3 4 41 0 0 0
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopUnavailableFfi]

def crepLoopFinalEvent : FfiFinalEvent :=
  { name := .extCall "halt", configuration := [41], bytes := [0],
    outcome := .failed }

def crepLoopFinalFfi : CrepFfiHandler Nat :=
  fun _ _ _ _ _ _ => some (.final crepLoopFinalEvent)

theorem crepToLoop_extCall_final_projection_regression :
    evalCrepFullResult [] (fun _ _ => none) crepLoopFinalFfi
        (fun _ _ _ _ => none) 0 100 4 crepLoopFfiState
        (.extCall "halt" 1 2 3 4) = none ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFinalFfi) 4
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.extCall "halt" 1 2 3 4)) = none := by
  apply crepToLoop_extCall_final_projection_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFinalFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState [9] "halt" 1 2 3 4 41 0 0 0
    crepLoopFinalEvent
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFinalFfi, crepLoopFinalEvent]

theorem crepToLoop_seq_extCall_final_projection_regression :
    evalCrepFullResult [] (fun _ _ => none) crepLoopFinalFfi
        (fun _ _ _ _ => none) 0 100 5 crepLoopFfiState
        (.seq (.extCall "halt" 1 2 3 4) (.return [.const 99])) = none ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFinalFfi) 5
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.seq (.extCall "halt" 1 2 3 4) (.return [.const 99]))) = none := by
  apply crepToLoop_seq_extCall_final_projection_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFinalFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState [9] "halt" 1 2 3 4 41 0 0 0
    crepLoopFinalEvent (.return [.const 99])
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFinalFfi, crepLoopFinalEvent]

theorem crepToLoop_seq_extCall_failure_regression :
    evalCrepFullProg [] (fun _ _ => none) crepLoopUnavailableFfi
        (fun _ _ _ _ => none) 0 100 5 crepLoopFfiState
        (.seq (.extCall "missing" 1 2 3 4) (.return [.const 99])) = none ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopUnavailableFfi) 5
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.seq (.extCall "missing" 1 2 3 4) (.return [.const 99]))) = none := by
  apply crepToLoop_seq_extCall_failure_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopUnavailableFfi (fun _ _ _ _ => none)
    0 100 3 crepLoopFfiState [9] "missing" 1 2 3 4 41 0 0 0
    (.return [.const 99])
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopUnavailableFfi]

theorem crepToLoop_return_raise_regression :
    (evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 1 crepLoopFfiState
        (.return [.const 42])).map crepControlValues =
        (evalLoopProgWithCallsAndFfi []
          (fun _ _ _ _ _ loopState => some loopState) 12
          (loopStateOfCrepState crepLoopFfiState)
          (loopCompileProg
            ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
              LoopContext Nat)
            [9] (.return [.const 42]))).map loopResultValues ∧
    (evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 1 crepLoopFfiState
        (.raise 17)).map crepControlException =
        (evalLoopProgWithCallsAndFfi []
          (fun _ _ _ _ _ loopState => some loopState) 8
          (loopStateOfCrepState crepLoopFfiState)
          (loopCompileProg
            ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
              LoopContext Nat)
            [9] (.raise 17))).map loopControlException := by
  constructor
  · exact crepToLoop_return_const_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
      [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
      0 100 0 crepLoopFfiState [9] 42
  · exact crepToLoop_raise_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
      [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
      0 100 0 crepLoopFfiState [9] 17

def crepCallSkipState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepCallSkipFunctions : List (CompiledFunction Nat) :=
  [{ name := "id", params := [], body := .skip, returnShape := .one }]

def crepCallSkipLoopFunctions : List (Nat × List Nat × LoopProg Nat) :=
  [(7, [], .skip)]

def crepCallSkipContext : LoopContext Nat :=
  { vars := [], functions := [("id", (7, 0))], maxVar := 0, target := .rv64i }

theorem crepToLoop_call_skip_regression :
    evalCrepFullProg crepCallSkipFunctions (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 100 4
        crepCallSkipState (.call none "id" []) =
        some (.normal crepCallSkipState) ∧
    evalLoopProgWithCallsAndFfi crepCallSkipLoopFunctions
        (loopFfiOfCrepFfi (fun _ _ _ _ _ _ => none)) 4
        (loopStateOfCrepState crepCallSkipState)
        (loopCompileProg crepCallSkipContext [9] (.call none "id" [])) =
        some (.normal (loopStateOfCrepState crepCallSkipState)) := by
  apply crepToLoop_call_skip_agreement crepCallSkipContext
    crepCallSkipFunctions crepCallSkipLoopFunctions
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 0 crepCallSkipState [9] "id" 7
  · simp [crepCallSkipFunctions, lookupCompiledFunction]
  · simp [crepCallSkipContext, lookupInfo]
  · simp [crepCallSkipLoopFunctions, lookupLoopFunction]

def crepCallReturnState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun _ => none }

def crepCallReturnFunctions : List (CompiledFunction Nat) :=
  [{ name := "id", params := [1], body := .return [.var 1], returnShape := .one }]

def crepCallReturnLoopFunctions : List (Nat × List Nat × LoopProg Nat) :=
  [(7, [1], .return [1])]

def crepCallReturnContext : LoopContext Nat :=
  { vars := [], functions := [("id", (7, 1))], maxVar := 0, target := .rv64i }

theorem crepToLoop_call_return_regression :
    (evalCrepFullProg crepCallReturnFunctions (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 100 8
        crepCallReturnState
        (.call (some ([8], none)) "id" [.const 42])).map
        (crepControlLocal 8) =
      (evalLoopProgWithCallsAndFfi crepCallReturnLoopFunctions
        (loopFfiOfCrepFfi (fun _ _ _ _ _ _ => none)) 8
        (loopStateOfCrepState crepCallReturnState)
        (loopCompileProg crepCallReturnContext [9]
          (.call (some ([8], none)) "id" [.const 42]))).map
        (loopControlLocal 8) := by
  apply crepToLoop_call_return_const_agreement crepCallReturnContext
    crepCallReturnFunctions crepCallReturnLoopFunctions
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 0 crepCallReturnState [9] "id" 7 1 8 42
  · simp [crepCallReturnFunctions, lookupCompiledFunction]
  · simp [crepCallReturnContext, lookupInfo]
  · simp [crepCallReturnLoopFunctions, lookupLoopFunction]

def crepHandlerFunctions : List (CompiledFunction Nat) :=
  [{ name := "raise", params := [], body := .raise 17, returnShape := .one }]

def crepHandlerLoopFunctions : List (Nat × List Nat × LoopProg Nat) :=
  [(7, [], loopCompileProg crepCallSkipContext [] (.raise 17))]

def crepHandlerContext : LoopContext Nat :=
  { vars := [], functions := [("raise", (7, 0))], maxVar := 0, target := .rv64i }

theorem crepToLoop_call_caught_skip_regression :
    (evalCrepFullProg crepHandlerFunctions (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 100 20
        crepCallSkipState
        (.call (some ([], some (17, .skip))) "raise" [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi crepHandlerLoopFunctions
        (loopFfiOfCrepFfi (fun _ _ _ _ _ _ => none)) 20
        (loopStateOfCrepState crepCallSkipState)
        (loopCompileProg crepHandlerContext [9]
          (.call (some ([], some (17, .skip))) "raise" []))).map
        loopResultValues := by
  apply crepToLoop_call_caught_skip_agreement crepHandlerContext
    crepHandlerFunctions crepHandlerLoopFunctions
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 0 crepCallSkipState [9] "raise" 7 17
  · simp [crepHandlerFunctions, lookupCompiledFunction]
  · simp [crepHandlerContext, lookupInfo]
  · simp [crepHandlerLoopFunctions, crepHandlerContext, crepCallSkipContext,
      loopCompileProg, lookupLoopFunction]

theorem crepToLoop_call_uncaught_regression :
    (evalCrepFullProg crepHandlerFunctions (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 100 20
        crepCallSkipState (.call none "raise" [])).map crepControlException =
      (evalLoopProgWithCallsAndFfi crepHandlerLoopFunctions
        (loopFfiOfCrepFfi (fun _ _ _ _ _ _ => none)) 20
        (loopStateOfCrepState crepCallSkipState)
        (loopCompileProg crepHandlerContext [9] (.call none "raise" []))).map
        loopControlException := by
  apply crepToLoop_call_uncaught_raise_agreement crepHandlerContext
    crepHandlerFunctions crepHandlerLoopFunctions
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 0 crepCallSkipState [9] "raise" 7 17
  · simp [crepHandlerFunctions, lookupCompiledFunction]
  · simp [crepHandlerContext, lookupInfo]
  · simp [crepHandlerLoopFunctions, crepHandlerContext, crepCallSkipContext,
      loopCompileProg, lookupLoopFunction]

theorem crepToLoop_call_caught_return_regression :
    (evalCrepFullProg crepHandlerFunctions (fun _ _ => none)
        (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none) 0 100 30
        crepCallSkipState
        (.call (some ([], some (17, .return [.const 42]))) "raise" [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi crepHandlerLoopFunctions
        (loopFfiOfCrepFfi (fun _ _ _ _ _ _ => none)) 30
        (loopStateOfCrepState crepCallSkipState)
        (loopCompileProg crepHandlerContext [9]
          (.call (some ([], some (17, .return [.const 42]))) "raise" []))).map
        loopResultValues := by
  apply crepToLoop_call_caught_return_const_agreement crepHandlerContext
    crepHandlerFunctions crepHandlerLoopFunctions
    (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 0 crepCallSkipState [9] "raise" 7 17 42
  · simp [crepHandlerFunctions, lookupCompiledFunction]
  · simp [crepHandlerContext, lookupInfo]
  · simp [crepHandlerLoopFunctions, crepHandlerContext, crepCallSkipContext,
      loopCompileProg, lookupLoopFunction]

theorem crepToLoop_seq_extCall_return_regression :
    (evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 20 crepLoopFfiState
        (.seq (.extCall "inc" 1 2 3 4) (.return [.const 99]))).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFfi) 20
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.seq (.extCall "inc" 1 2 3 4) (.return [.const 99])))).map
        loopResultValues := by
  apply crepToLoop_seq_extCall_return_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } : LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
    0 100 0 crepLoopFfiState crepLoopFfiStateAfter [9] "inc" 1 2 3 4
    41 0 0 0 99
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfi, crepLoopFfiState, crepLoopFfiStateAfter]

theorem crepToLoop_seq_extCall_raise_regression :
    evalCrepFullProg [] (fun _ _ => none) crepLoopFfi
        (fun _ _ _ _ => none) 0 100 20 crepLoopFfiState
        (.seq (.extCall "inc" 1 2 3 4) (.raise 17)) =
      some (.raised crepLoopFfiStateAfter 17) ∧
    evalLoopProgWithCallsAndFfi [] (loopFfiOfCrepFfi crepLoopFfi) 20
        (loopStateOfCrepState crepLoopFfiState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [9] (.seq (.extCall "inc" 1 2 3 4) (.raise 17))) =
      some (.raised
        { (loopStateOfCrepState crepLoopFfiStateAfter) with
          locals := updateLoopLocal crepLoopFfiStateAfter.locals 1 17 } 17) := by
  apply crepToLoop_seq_extCall_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
    0 100 18 crepLoopFfiState crepLoopFfiStateAfter [9] "inc" 1 2 3 4
    41 0 0 0 (.raise 17) (.raised crepLoopFfiStateAfter 17)
      (.raised
        { (loopStateOfCrepState crepLoopFfiStateAfter) with
          locals := updateLoopLocal crepLoopFfiStateAfter.locals 1 17 } 17)
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfiState]
  · simp [crepLoopFfi, crepLoopFfiState, crepLoopFfiStateAfter]
  · simp [evalCrepFullProg, crepLoopFfiStateAfter]
  · simp [loopCompileProg, evalLoopProgWithCallsAndFfi, evalLoopProg,
      evalLoopExp, updateLoopLocal, loopStateOfCrepState]

end Flapjack
