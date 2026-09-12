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

def crepZeroConditionState : CrepState Nat :=
  { crepSeqInitial with
    locals := updateCrepLocal crepSeqInitial.locals 1 0 }

def crepOneConditionState : CrepState Nat :=
  { crepSeqInitial with
    locals := updateCrepLocal crepSeqInitial.locals 1 1 }

def crepStoreExpressionState : CrepState Nat :=
  { locals := fun name =>
      if name == 1 then some 200
      else if name == 2 then some 42
      else none
    memory := fun _ => none }

def crepLoadExpressionState : CrepState Nat :=
  { locals := fun name => if name == 1 then some 100 else none
    memory := fun address => if address == 100 then some 42 else none }

def crepSeqMiddle : CrepState Nat :=
  { crepSeqInitial with
    locals := updateCrepLocal crepSeqInitial.locals 5 42 }

def crepSeqFinal : CrepState Nat :=
  { crepSeqMiddle with
    locals := updateCrepLocal crepSeqMiddle.locals 6 42 }

def crepLoopPrimitiveState : CrepState Nat :=
  { locals := fun name =>
      if name == 1 then some 10
      else if name == 2 then some 32
      else if name == 3 then some 0
      else none
    memory := fun _ => none }

def crepLoopAddPrimitive : CrepPrimitiveHandler Nat :=
  fun operator arguments =>
    match operator, arguments with
    | .addCarry, [left, right, carry] => some [left + right, carry]
    | _, _ => none

theorem crepToLoop_primitive_regression :
    (evalCrepFullProg [] crepLoopAddPrimitive (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopPrimitiveState
      (.primitive [5, 6] .addCarry [1, 2, 3])).map (crepControlLocal 5) =
    (evalLoopProgWithPrimitiveCallsAndFfi crepLoopAddPrimitive []
      (fun _ _ _ _ _ loopState => some loopState) 3
      (loopStateOfCrepState crepLoopPrimitiveState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.primitive [5, 6] .addCarry [1, 2, 3]))).map (loopControlLocal 5) := by
  exact crepToLoop_full_primitive_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] crepLoopAddPrimitive (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ loopState => some loopState) (fun _ _ _ _ => none)
    0 100 2 crepLoopPrimitiveState [] [5, 6] .addCarry [1, 2, 3] 5

theorem crepToLoop_primitive_correctness_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.const (42 : Nat)] : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_return_const 42

theorem crepToLoop_primitive_assign_load_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.load (.var 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_load_var 2 1

theorem crepToLoop_primitive_assign_load32_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.load32 (.var 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_load32_var 2 1

theorem crepToLoop_primitive_assign_loadByte_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.loadByte (.var 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_loadByte_var 2 1

theorem crepToLoop_primitive_store_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.store (.const (200 : Nat)) (.var 1) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_store_var 200 1

theorem crepToLoop_primitive_assign_add_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .add [.var 0, .var 1]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_add_var_var 2 0 1

theorem crepToLoop_primitive_assign_sub_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .sub [.var 0, .var 1]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_sub_var_var 2 0 1

theorem crepToLoop_primitive_assign_and_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .and [.var 0, .var 1]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_and_var_var 2 0 1

theorem crepToLoop_primitive_assign_or_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .or [.var 0, .var 1]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_or_var_var 2 0 1

theorem crepToLoop_primitive_assign_xor_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .xor [.var 0, .var 1]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_xor_var_var 2 0 1

theorem crepToLoop_primitive_assign_lsl_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.shift .lsl (.var 0) (.var 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_lsl_var_var 2 0 1

theorem crepToLoop_primitive_assign_lsr_var_var_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.shift .lsr (.var 0) (.var 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_lsr_var_var 2 0 1

theorem crepToLoop_primitive_assign_cmp_equal_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .equal (.const (3 : Nat)) (.const 3)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_equal_const 2 3 3

theorem crepToLoop_primitive_assign_cmp_notEqual_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .notEqual (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_notEqual_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_lower_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .lower (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_lower_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_less_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .less (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_less_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_notLower_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .notLower (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_notLower_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_notLess_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .notLess (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_notLess_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_test_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .test (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_test_const 2 3 4

theorem crepToLoop_primitive_assign_cmp_notTest_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.cmp .notTest (.const (3 : Nat)) (.const 4)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_cmp_notTest_const 2 3 4

theorem crepToLoop_primitive_assign_and_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.op .and [.const (3 : Nat), .const 4]) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_binop_const_const 2 .and 3 4

theorem crepToLoop_primitive_assign_lsl_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.shift .lsl (.const (3 : Nat)) (.const 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_lsl_const_const 2 3 1

theorem crepToLoop_primitive_assign_lsr_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign 2 (.shift .lsr (.const (8 : Nat)) (.const 1)) : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_assign_lsr_const_const 2 8 1

theorem crepToLoop_primitive_return_or_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.op .or [.const (3 : Nat), .const 4]] : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_return_binop_const_const .or 3 4

theorem crepToLoop_primitive_return_lsl_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.shift .lsl (.const (3 : Nat)) (.const 1)] : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_return_lsl_const_const 3 1

theorem crepToLoop_primitive_return_lsr_const_const_contract_regression :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.shift .lsr (.const (8 : Nat)) (.const 1)] : CrepProg Nat) := by
  exact crepToLoopProgramCorrectWithPrimitive_return_lsr_const_const 8 1

theorem crepToLoop_store32_var_contract_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.store32 (.const 200) (.var 5))).map
        (crepControlMemoryAt 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
          LoopContext Nat)
        [] (.store32 (.const 200) (.var 5)))).map
        (loopControlMemoryAt 200) := by
  exact crepToLoop_store32_var_agreement
    ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 2 crepLoopAssignState [] 200 5 (by change 5 ≤ 5; omega)

theorem crepToLoop_store_var_address_contract_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.store (.var 5) (.const 42))).map
        (crepControlMemoryAt 1) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      6 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
          LoopContext Nat)
        [] (.store (.var 5) (.const 42)))).map
        (loopControlMemoryAt 1) := by
  exact crepToLoop_store_var_address_agreement
    ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 2 crepLoopAssignState [] 1 5 42
    (by change 5 ≤ 5; omega) (by simp [crepLoopAssignState])

theorem crepToLoop_storeByte_var_contract_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.storeByte (.const 201) (.var 5))).map
        (crepControlMemoryAt 201) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
          LoopContext Nat)
        [] (.storeByte (.const 201) (.var 5)))).map
        (loopControlMemoryAt 201) := by
  exact crepToLoop_storeByte_var_agreement
    ({ vars := [], functions := [], maxVar := 5, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    0 100 2 crepLoopAssignState [] 201 5 (by change 5 ≤ 5; omega)

theorem crepToLoop_primitive_seq_normal_regression :
    evalCrepFullProg [] (fun _ _ => none)
        (fun _ _ _ _ _ state => some (.returned state))
        (fun _ _ _ _ => none) 0 100 4 crepSeqInitial
        (.seq (.assign 5 (.const 42)) (.assign 6 (.var 5))) =
      some (.normal crepSeqFinal) ∧
    evalLoopProgWithPrimitiveCallsAndFfi (fun _ _ => none) []
        (fun _ _ _ _ _ loopState => some loopState)
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
  apply crepToLoopWithPrimitive_seq_normal_compose
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) (fun _ _ _ _ _ state => some (.returned state))
    (fun _ _ _ _ _ loopState => some loopState) (fun _ _ _ _ => none)
    0 100 2 crepSeqInitial crepSeqMiddle []
    (.assign 5 (.const 42) : CrepProg Nat)
    (.assign 6 (.var 5) : CrepProg Nat)
    (.normal crepSeqFinal : CrepControlResult Nat)
    (.normal (loopStateOfCrepState crepSeqFinal) : LoopResult Nat)
  all_goals simp [crepSeqInitial, crepSeqMiddle, crepSeqFinal,
    loopStateOfCrepState, updateCrepLocal, hupdate,
    evalCrepFullProg, evalCrepFullExp, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
    evalLoopExp]

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

theorem crepToLoop_seq_terminal_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 100 4 crepSeqInitial
        (.seq (.break 0) (.assign 5 (.const 42))) =
      some (.broke crepSeqInitial 0) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        4 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.seq (.break 0) (.assign 5 (.const 42)))) =
      some (.broke (loopStateOfCrepState crepSeqInitial) 0) := by
  apply crepToLoop_seq_terminal_compose
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ loopState => some loopState) (fun _ _ _ _ => none)
    0 100 2 crepSeqInitial [] (.break 0) (.assign 5 (.const 42))
    (.broke crepSeqInitial 0) (.broke (loopStateOfCrepState crepSeqInitial) 0)
  · simp [crepSeqInitial, evalCrepFullProg]
  · simp [crepSeqInitial, loopStateOfCrepState, loopCompileProg,
      evalLoopProgWithCallsAndFfi, evalLoopProg]
  · intro middle h
    cases h
  · intro middle h
    cases h

def crepLoopLoadState : CrepState Nat :=
  { locals := fun name => if name == 5 then some 1 else none
    memory := fun address => if address == 100 then some 42 else none }

def crepLoopSharedStoreState : CrepState Nat :=
  { locals := fun name => if name == 5 then some 42 else none
    memory := fun _ => none }

def crepLoopRuntimeGlobalState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
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

def crepLoopRuntimeHandler : CrepRuntimeFfiHandler Nat Unit Unit :=
  fun _ state => .returned state

def crepLoopRuntimeGlobalLoadState : CrepRuntimeState Nat Unit :=
  { crepLoopRuntimeGlobalState with
    globals := fun address => if address == 200 then some 42 else none }

theorem crepRuntimeToLoop_storeGlob_regression :
    (evalCrepRuntimeResult crepLoopRuntimeHandler (fun _ _ => none) 2
      crepLoopRuntimeGlobalState (.storeGlob 200 (.const 42))).map
        (fun result => result.2.globals 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeState crepLoopRuntimeGlobalState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.storeGlob 200 (.const 42)))).map
        (fun result => (loopResultState result).globals 200) := by
  exact crepRuntimeToLoop_storeGlob_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] crepLoopRuntimeHandler (fun _ _ => none) 1
    crepLoopRuntimeGlobalState [] 200 42

theorem crepRuntimeToLoop_loadGlob_regression :
    (evalCrepRuntimeResult crepLoopRuntimeHandler (fun _ _ => none) 2
      crepLoopRuntimeGlobalLoadState
      (.assign 5 (.loadGlob 200))).map
        (fun result => result.2.locals 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      3 (loopStateOfCrepRuntimeState crepLoopRuntimeGlobalLoadState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.assign 5 (.loadGlob 200)))).map
        (fun result => (loopResultState result).locals 5) := by
  apply crepRuntimeToLoop_loadGlob_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] crepLoopRuntimeHandler (fun _ _ => none) 1
    crepLoopRuntimeGlobalLoadState [] 5 200 42
  simp [crepLoopRuntimeGlobalLoadState]

theorem crepRuntimeToLoop_store_load_regression :
    (evalCrepRuntimeResult crepLoopRuntimeHandler (fun _ _ => none) 6
      crepLoopRuntimeGlobalState
      (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200)))).map
        (fun result => result.2.locals 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      12 (loopStateOfCrepRuntimeState crepLoopRuntimeGlobalState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.seq (.storeGlob 200 (.const 42)) (.assign 5 (.loadGlob 200))))).map
        (fun result => (loopResultState result).locals 5) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeState, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopResultState, updateMemory, updateLoopGlobal,
    updateCrepLocal, updateLoopLocal]

theorem crepToLoop_while_zero_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial
      (.while (.const 0) (.assign 5 (.const 42)))).map
        (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      13 (loopStateOfCrepState crepSeqInitial)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.while (.const 0) (.assign 5 (.const 42))))).map
        (loopControlLocal 5) := by
  exact crepToLoop_while_const_zero_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepSeqInitial [] 5
    (.assign 5 (.const 42)) (by decide)

theorem crepToLoop_control_regressions :
    ((evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial (.skip)).map
        (crepControlLocal 5) =
      (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        2 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat) [] (.skip))).map (loopControlLocal 5)) ∧
    ((evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial (.tick)).map
        (crepControlLocal 5) =
      (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        2 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat) [] (.tick))).map (loopControlLocal 5)) ∧
    ((evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial (.break 3)).map
        (crepControlLocal 5) =
      (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        2 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat) [] (.break 3))).map (loopControlLocal 5)) ∧
    ((evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial (.continue 3)).map
        (crepControlLocal 5) =
      (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        2 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat) [] (.continue 3))).map (loopControlLocal 5)) := by
  constructor
  · exact crepToLoop_skip_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
        LoopContext Nat)
      [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqInitial [] 5
  constructor
  · exact crepToLoop_tick_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
        LoopContext Nat)
      [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqInitial [] 5
  constructor
  · exact crepToLoop_break_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
        LoopContext Nat)
      [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqInitial [] 3 5
  · exact crepToLoop_continue_agreement
      ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
        LoopContext Nat)
      [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqInitial [] 3 5

theorem crepToLoop_ite_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 4 crepSeqInitial
      (.ite (.const 1) (.assign 5 (.const 42)) (.assign 5 (.const 0)))).map
        (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      10 (loopStateOfCrepState crepSeqInitial)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.ite (.const 1) (.assign 5 (.const 42)) (.assign 5 (.const 0))))).map
        (loopControlLocal 5) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    evalLoopCondition]

theorem crepToLoop_ite_zero_compose_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 100 2 crepSeqInitial
        (.ite (.const 0) (.skip) (.assign 5 (.const 42))) =
      some (.normal crepSeqMiddle) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        6 (loopStateOfCrepState crepSeqInitial)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.ite (.const 0) (.skip) (.assign 5 (.const 42)))) =
      some (.normal
        { loopStateOfCrepState crepSeqInitial with
          locals := updateLoopLocal
            (updateLoopLocal crepSeqInitial.locals 1 0) 5 42 }) := by
  apply crepToLoop_ite_const_zero_compose
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepSeqInitial []
    (.skip) (.assign 5 (.const 42))
    (.normal
      { crepSeqInitial with
        locals := updateCrepLocal crepSeqInitial.locals 5 42 })
    (.normal
      { loopStateOfCrepState crepSeqInitial with
        locals := updateLoopLocal
          (updateLoopLocal crepSeqInitial.locals 1 0) 5 42 })
  · simp [crepSeqInitial, evalCrepFullProg, evalCrepFullExp]
  · simp [crepSeqInitial, loopStateOfCrepState, loopCompileProg,
      loopCompileExp, loopNestedSeq, evalLoopProgWithCallsAndFfi,
      evalLoopProg, evalLoopExp]

theorem crepToLoop_ite_var_false_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 100 2 crepZeroConditionState
        (.ite (.var 1) (.skip) (.assign 5 (.const 42))) =
      some (.normal
        { crepZeroConditionState with
          locals := updateCrepLocal crepZeroConditionState.locals 5 42 }) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        6 (loopStateOfCrepState crepZeroConditionState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.ite (.var 1) (.skip) (.assign 5 (.const 42)))) =
      some (.normal
        { loopStateOfCrepState crepZeroConditionState with
          locals := updateLoopLocal
            (updateLoopLocal crepZeroConditionState.locals 1 0) 5 42 }) := by
  apply crepToLoop_ite_false_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepZeroConditionState []
    (.var 1) (.skip) (.assign 5 (.const 42))
    (.normal
      { crepZeroConditionState with
        locals := updateCrepLocal crepZeroConditionState.locals 5 42 })
    (.normal
      { loopStateOfCrepState crepZeroConditionState with
        locals := updateLoopLocal
          (updateLoopLocal crepZeroConditionState.locals 1 0) 5 42 })
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepZeroConditionState, crepSeqInitial, evalCrepFullExp,
      updateCrepLocal]
  · simp [crepZeroConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileExp, evalLoopExp, updateCrepLocal]
  · simp [crepZeroConditionState, crepSeqInitial, evalCrepFullProg,
      evalCrepFullExp]
  · simp [crepZeroConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp]

theorem crepToLoop_ite_var_true_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        (fun _ _ _ _ => none) 0 100 2 crepOneConditionState
        (.ite (.var 1) (.assign 5 (.const 42)) (.skip)) =
      some (.normal
        { crepOneConditionState with
          locals := updateCrepLocal crepOneConditionState.locals 5 42 }) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        6 (loopStateOfCrepState crepOneConditionState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
            LoopContext Nat)
          [] (.ite (.var 1) (.assign 5 (.const 42)) (.skip))) =
      some (.normal
        { loopStateOfCrepState crepOneConditionState with
          locals := updateLoopLocal
            (updateLoopLocal crepOneConditionState.locals 1 1) 5 42 }) := by
  apply crepToLoop_ite_true_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepOneConditionState []
    (.var 1) (.assign 5 (.const 42)) (.skip)
    (.normal
      { crepOneConditionState with
        locals := updateCrepLocal crepOneConditionState.locals 5 42 })
    (.normal
      { loopStateOfCrepState crepOneConditionState with
        locals := updateLoopLocal
          (updateLoopLocal crepOneConditionState.locals 1 1) 5 42 })
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepOneConditionState, crepSeqInitial, evalCrepFullExp,
      updateCrepLocal]
  · simp
  · simp [crepOneConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileExp, evalLoopExp, updateCrepLocal]
  · simp [crepOneConditionState, crepSeqInitial, evalCrepFullProg,
      evalCrepFullExp]
  · simp [crepOneConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp]

theorem crepToLoop_while_var_false_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepZeroConditionState
      (.while (.var 1) (.assign 5 (.const 42)))).map
        (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 13
      (loopStateOfCrepState crepZeroConditionState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.while (.var 1) (.assign 5 (.const 42))))).map
        (loopControlLocal 5) := by
  apply crepToLoop_while_false_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepZeroConditionState []
    (.var 1) (.assign 5 (.const 42)) 5
  · decide
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepZeroConditionState, crepSeqInitial, evalCrepFullExp,
      updateCrepLocal]
  · simp [crepZeroConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileExp, evalLoopExp, updateCrepLocal]

theorem crepToLoop_while_var_true_break_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepOneConditionState
      (.while (.var 1) (.break 0))).map
        (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 13
      (loopStateOfCrepState crepOneConditionState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
          LoopContext Nat)
        [] (.while (.var 1) (.break 0)))).map
        (loopControlLocal 5) := by
  apply crepToLoop_while_true_break_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 0 crepOneConditionState []
    (.var 1) 5
  · decide
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepOneConditionState, crepSeqInitial, evalCrepFullExp,
      updateCrepLocal]
  · simp [crepOneConditionState, crepSeqInitial, loopStateOfCrepState,
      loopCompileExp, evalLoopExp, updateCrepLocal]

theorem crepToLoop_store_var_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepStoreExpressionState
      (.store (.var 1) (.var 2))).map (crepControlMemoryAt 200) =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 5
      (loopStateOfCrepState crepStoreExpressionState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
          LoopContext Nat)
        [] (.store (.var 1) (.var 2)))).map (loopControlMemoryAt 200) := by
  apply crepToLoop_store_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 1 crepStoreExpressionState []
    (.var 1) (.var 2) 200 42
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepStoreExpressionState, evalCrepFullExp]
  · simp [crepStoreExpressionState, evalCrepFullExp]
  · simp [crepStoreExpressionState, loopStateOfCrepState,
      loopCompileExp, evalLoopExp]
  · simp [crepStoreExpressionState, loopStateOfCrepState,
      loopCompileExp, evalLoopExp]
  · simp [crepStoreExpressionState, loopCompileExp, evalLoopExp,
      updateLoopLocal]

theorem crepToLoop_shMem_store_var_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        defaultCrepSharedMemHandler 0 100 2 crepStoreExpressionState
        (.shMem .store 2 (.var 1)) =
      some (.normal
        { crepStoreExpressionState with
          memory := updateMemory crepStoreExpressionState.memory 200 42 }) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        3 (loopStateOfCrepState crepStoreExpressionState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
            LoopContext Nat)
          [] (.shMem .store 2 (.var 1))) =
      some (.normal
        (loopStateOfCrepState
          { crepStoreExpressionState with
            memory := updateMemory crepStoreExpressionState.memory 200 42 })) := by
  apply crepToLoop_shMem_store_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    defaultCrepSharedMemHandler 0 100 1 crepStoreExpressionState
    { crepStoreExpressionState with
      memory := updateMemory crepStoreExpressionState.memory 200 42 } []
    .store 2 (.var 1) 200 42
  · simp
  · simp [loopCompileExp]
  · simp [crepStoreExpressionState, evalCrepFullExp]
  · simp [crepStoreExpressionState, loopStateOfCrepState,
      loopCompileExp, evalLoopExp]
  · simp [crepStoreExpressionState]
  · simp [defaultCrepSharedMemHandler, crepStoreExpressionState]
  · rfl

theorem crepToLoop_primitive_shMem_store_seq_regression :
    evalCrepFullProg [] (fun _ _ => none)
        (fun _ _ _ _ _ state => some (.returned state))
        defaultCrepSharedMemHandler 0 100 3 crepStoreExpressionState
        (.seq (.shMem .store 2 (.const 200)) (.skip)) =
      some (.normal
        { crepStoreExpressionState with
          memory := updateMemory crepStoreExpressionState.memory 200 42 }) ∧
    evalLoopProgWithPrimitiveCallsAndFfi (fun _ _ => none) []
        (loopFfiOfCrepFfi (fun _ _ _ _ _ state => some (.returned state))) 4
        (loopStateOfCrepState crepStoreExpressionState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
            LoopContext Nat)
          [] (.seq (.shMem .store 2 (.const 200)) (.skip))) =
      some (.normal
        (loopStateOfCrepState
          { crepStoreExpressionState with
            memory := updateMemory crepStoreExpressionState.memory 200 42 })) := by
  apply crepToLoopWithPrimitive_shMem_store_seq_agreement
    ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none)
    (fun _ _ _ _ _ state => some (.returned state)) defaultCrepSharedMemHandler
    0 100 1 crepStoreExpressionState
    { crepStoreExpressionState with
      memory := updateMemory crepStoreExpressionState.memory 200 42 } []
    .store 2 200 42 (.skip : CrepProg Nat)
    (.normal
      { crepStoreExpressionState with
        memory := updateMemory crepStoreExpressionState.memory 200 42 })
    (.normal
      (loopStateOfCrepState
        { crepStoreExpressionState with
          memory := updateMemory crepStoreExpressionState.memory 200 42 }))
  all_goals simp [crepStoreExpressionState, defaultCrepSharedMemHandler,
    loopStateOfCrepState, loopCompileProg, evalCrepFullProg,
    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg]

theorem crepToLoop_shMem_load_var_regression :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        defaultCrepSharedMemHandler 0 100 2 crepLoadExpressionState
        (.shMem .load 2 (.var 1)) =
      some (.normal
        { crepLoadExpressionState with
          locals := updateCrepLocal crepLoadExpressionState.locals 2 42 }) ∧
    evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
        3 (loopStateOfCrepState crepLoadExpressionState)
        (loopCompileProg
          ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
            LoopContext Nat)
          [] (.shMem .load 2 (.var 1))) =
      some (.normal
        (loopStateOfCrepState
          { crepLoadExpressionState with
            locals := updateCrepLocal crepLoadExpressionState.locals 2 42 })) := by
  apply crepToLoop_shMem_load_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 2, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    defaultCrepSharedMemHandler 0 100 1 crepLoadExpressionState
    { crepLoadExpressionState with
      locals := updateCrepLocal crepLoadExpressionState.locals 2 42 } []
    .load 2 (.var 1) 100 42
  · simp
  · simp [loopCompileExp]
  · simp [crepLoadExpressionState, evalCrepFullExp]
  · simp [crepLoadExpressionState, loopStateOfCrepState,
      loopCompileExp, evalLoopExp]
  · simp [crepLoadExpressionState]
  · simp [defaultCrepSharedMemHandler, crepLoadExpressionState]
  · rfl

theorem crepToLoop_dec_return_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial
      (.dec 5 (.const 42) (.return [.var 5]))).map crepControlValues =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 20
      (loopStateOfCrepState crepSeqInitial)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.dec 5 (.const 42) (.return [.var 5])))).map loopResultValues ∧
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial
      (.dec 5 (.const 42) (.return [.var 5]))).map crepControlValues =
      some [42] := by
  have h := crepToLoop_dec_return_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 0 crepSeqInitial [] 5 (.const 42) 42
    (by simp [loopCompileExp])
    (by simp [crepSeqInitial, evalCrepFullExp])
    (by simp [crepSeqInitial, loopStateOfCrepState, loopCompileExp,
      evalLoopExp])
  constructor
  · simpa [crepSeqInitial] using h
  · simp [crepSeqInitial, evalCrepFullProg, evalCrepFullExps,
      evalCrepFullExp, crepControlValues, updateCrepLocal,
      restoreCrepResult]

theorem crepToLoop_dec_compose_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 2 crepSeqInitial
      (.dec 5 (.const 42) (.return [.var 5]))).map crepControlValues =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 20
      (loopStateOfCrepState crepSeqInitial)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.dec 5 (.const 42) (.return [.var 5])))).map loopResultValues := by
  apply crepToLoop_dec_compose_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 0 crepSeqInitial [] 5
    (.const 42) (.return [.var 5]) 42
    (.returned
      { crepSeqInitial with
        locals := updateCrepLocal crepSeqInitial.locals 5 42 } [42])
    (.returned
      { loopStateOfCrepState crepSeqInitial with
        locals := updateLoopLocal
          (updateLoopLocal crepSeqInitial.locals 5 42) 2 42 } [42])
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [loopCompileExp]
  · simp [crepSeqInitial, evalCrepFullExp]
  · simp [crepSeqInitial, loopStateOfCrepState, loopCompileExp,
      evalLoopExp]
  · simp [crepSeqInitial, evalCrepFullProg, evalCrepFullExps,
      evalCrepFullExp, updateCrepLocal]
  · simp [crepSeqInitial, loopStateOfCrepState, loopCompileProg,
      loopCompileExp, loopCompileExp.loopCompileExps, loopCompileExps,
      loopNestedSeq, loopTempNames, loopAssignTemps,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopReadLocals, updateLoopLocal]
  · rfl

theorem crepToLoop_return_var_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqMiddle
      (.return [.var 5])).map crepControlValues =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) 12
      (loopStateOfCrepState crepSeqMiddle)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.return [.var 5]))).map loopResultValues ∧
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 1 crepSeqMiddle
      (.return [.var 5])).map crepControlValues = some [42] := by
  have h := crepToLoop_return_of_empty_prefix
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 0 crepSeqMiddle [] (.var 5) 42
    (by simp [loopCompileExp])
    (by simp [crepSeqMiddle, evalCrepFullExp, updateCrepLocal])
    (by simp [crepSeqMiddle, loopStateOfCrepState, loopCompileExp,
      evalLoopExp, updateCrepLocal])
  constructor
  · simpa [crepSeqMiddle] using h
  · simp [crepSeqMiddle, evalCrepFullProg, evalCrepFullExps,
      evalCrepFullExp, crepControlValues, updateCrepLocal]

theorem crepToLoop_shMem_store_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      defaultCrepSharedMemHandler 0 100 3 crepLoopSharedStoreState
      (.shMem .store 5 (.const 200))).map
        (crepControlMemoryAt 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4 (loopStateOfCrepState crepLoopSharedStoreState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.shMem .store 5 (.const 200)))).map
        (loopControlMemoryAt 200) := by
  apply crepToLoop_shMem_store_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    defaultCrepSharedMemHandler 0 100 2 crepLoopSharedStoreState
    ({ crepLoopSharedStoreState with
      memory := updateMemory crepLoopSharedStoreState.memory 200 42 }) []
    .store 5 200 42
    (Or.inl rfl)
  · simp [crepLoopSharedStoreState]
  · simp [defaultCrepSharedMemHandler, crepLoopSharedStoreState]
  · rfl

theorem crepToLoop_shMem_load_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      defaultCrepSharedMemHandler 0 100 3 crepLoopLoadState
      (.shMem .load 5 (.const 100))).map (crepControlLocal 5) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      4 (loopStateOfCrepState crepLoopLoadState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.shMem .load 5 (.const 100)))).map (loopControlLocal 5) := by
  apply crepToLoop_shMem_load_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    defaultCrepSharedMemHandler 0 100 2 crepLoopLoadState
    ({ crepLoopLoadState with
      locals := updateCrepLocal crepLoopLoadState.locals 5 42 }) []
    .load 5 100 42
    (Or.inl rfl)
  · simp [crepLoopLoadState]
  · simp [defaultCrepSharedMemHandler, crepLoopLoadState]
  · rfl

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

theorem crepToLoop_store32_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.store32 (.const 200) (.const 43))).map
        (crepControlMemoryAt 200) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.store32 (.const 200) (.const 43)))).map
        (loopControlMemoryAt 200) := by
  exact crepToLoop_store32_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopAssignState [] 200 43

theorem crepToLoop_storeByte_const_regression :
    (evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      (fun _ _ _ _ => none) 0 100 3 crepLoopAssignState
      (.storeByte (.const 201) (.const 44))).map
        (crepControlMemoryAt 201) =
    (evalLoopProgWithCallsAndFfi [] (fun _ _ _ _ _ loopState => some loopState)
      7 (loopStateOfCrepState crepLoopAssignState)
      (loopCompileProg
        ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
          LoopContext Nat)
        [] (.storeByte (.const 201) (.const 44)))).map
        (loopControlMemoryAt 201) := by
  exact crepToLoop_storeByte_const_agreement
    ({ vars := [], functions := [], maxVar := 0, target := .rv64i } :
      LoopContext Nat)
    [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none) 0 100 2 crepLoopAssignState [] 201 44

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

theorem crepToLoop_call_caught_ffi_handler_regression :
    (evalCrepFullProg crepHandlerFunctions (fun _ _ => none)
        crepLoopFfi (fun _ _ _ _ => none) 0 100 4 crepLoopFfiState
        (.call (some ([], some (17, .extCall "inc" 1 2 3 4))) "raise" [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi
        [(7, [], loopCompileProg crepHandlerContext [] (.raise 17))]
        (loopFfiOfCrepFfi crepLoopFfi) 4
        (loopStateOfCrepState crepLoopFfiState)
        (.call (some ([], [])) (some 7) []
          (some (8, loopCompileProg crepHandlerContext []
            (.extCall "inc" 1 2 3 4), .skip, [])))).map
        loopResultValues := by
  apply crepToLoop_call_caught_handler_agreement
    crepHandlerFunctions
    [(7, [], loopCompileProg crepHandlerContext [] (.raise 17))]
    (fun _ _ => none) crepLoopFfi (fun _ _ _ _ => none)
    0 100 2 crepLoopFfiState (loopStateOfCrepState crepLoopFfiState)
    "raise" 7 8 17 17
    (.raise 17)
    (loopCompileProg crepHandlerContext [] (.raise 17))
    (.extCall "inc" 1 2 3 4)
    (loopCompileProg crepHandlerContext [] (.extCall "inc" 1 2 3 4))
    { locals := fun _ => none, memory := crepLoopFfiState.memory }
    { locals := updateLoopLocal (fun _ => none) 1 17,
      globals := fun _ => none,
      memory := crepLoopFfiState.memory }
    (.normal
      { crepLoopFfiState with
        locals := updateCrepLocal crepLoopFfiState.locals 9 42 })
    (.normal
      { loopStateOfCrepState crepLoopFfiState with
        locals := updateLoopLocal
          (updateLoopLocal
            (loopStateOfCrepState crepLoopFfiState).locals 8 17) 9 42 })
  · rfl
  · simp [crepHandlerFunctions, lookupCompiledFunction]
  · simp [lookupLoopFunction]
  · decide
  · simp [crepHandlerFunctions, evalCrepFullProg]
  · simp [crepHandlerContext,
      loopCompileProg, evalLoopProgWithCallsAndFfi, evalLoopProg,
      evalLoopExp, updateLoopLocal, loopStateOfCrepState]
    funext current
    rfl
  · apply evalCrepFullProg_extCall
      crepHandlerFunctions (fun _ _ => none) crepLoopFfi
      (fun _ _ _ _ => none) 0 100 1
      { locals := crepLoopFfiState.locals,
        memory := crepLoopFfiState.memory }
      { crepLoopFfiState with
        locals := updateCrepLocal crepLoopFfiState.locals 9 42 }
      "inc" 1 2 3 4 41 0 0 0
    · simp [crepLoopFfiState]
    · simp [crepLoopFfiState]
    · simp [crepLoopFfiState]
    · simp [crepLoopFfiState]
    · simp [crepLoopFfi, crepLoopFfiState]
  · rw [loopCompileProg_extCall]
    rw [evalLoopProgWithCallsAndFfi_ffi]
    simp [crepLoopFfi, crepLoopFfiState, loopFfiOfCrepFfi,
      crepStateOfLoopState, updateLoopLocal, loopStateOfCrepState]
    funext current
    by_cases h9 : current = 9
    · simp [updateCrepLocal, updateLoopLocal, h9]
    · by_cases h8 : current = 8
      · subst current
        simp [updateCrepLocal, updateLoopLocal]
      · simp [updateCrepLocal, updateLoopLocal, h9, h8]
  · rfl

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
