import Flapjack.Test.Calls

namespace Flapjack

open RiscV

def loopCallTestState : LoopState Nat :=
  { locals := fun name => if name = 1 then some 9 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopSharedMemoryTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 100 else if name = 2 then some 42 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 10 else if name = 2 then some 1
      else if name = 3 then some 20 else if name = 4 then some 2 else none
    globals := fun _ => none
    memory := fun _ => none }

def loopFfiTestHandler : FunName → Nat → Nat → Nat → Nat → LoopState Nat →
    Option (LoopState Nat) := fun function configuration configurationLength array arrayLength state =>
  if function == "sum" then
    let value := configuration + configurationLength + array + arrayLength
    some { state with locals := updateLoopLocal state.locals 5 value }
  else none

def loopAddCarryState : LoopState (RiscV.Word 64) :=
  { locals := fun name =>
      if name == 2 then some (BitVec.ofNat 64 1)
      else if name == 3 then some (BitVec.ofNat 64 2)
      else if name == 4 then some (BitVec.ofNat 64 0)
      else none
    globals := fun _ => none
    memory := fun _ => none }

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result => ((loopResultState result).locals 5,
          (loopResultState result).locals 6)) =
      some (some (BitVec.ofNat 64 3), some (BitVec.ofNat 64 0)) := by
  native_decide

def loopAddCarryMachineState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeRegister
      (RiscV.writeRegister (RiscV.zeroState 64) 2 1) 3 2) 4 0

example :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1
      loopAddCarryState (.primitive [5, 6] .addCarry [2, 3, 4])).map
        (fun result => ((loopResultState result).locals 5,
          (loopResultState result).locals 6)) =
      (RiscV.evalWordFunction loopAddCarryMachineState
        (loopToWordProg ({ vars := [] } : WordContext)
          (.primitive [5, 6] .addCarry [2, 3, 4]))).map
        (fun result => (some (RiscV.readRegister result.1 5),
          some (RiscV.readRegister result.1 6))) := by
  native_decide

def addCarrySourceLocals : VarName → Option (PanValue (RiscV.Word 64)) :=
  fun name =>
    if name == "result" then
      some (.rStruct [.word 0, .word 0])
    else none

def addCarrySource : Prog (RiscV.Word 64) :=
  .primitive "result" .addCarry
    [.const 1, .const 2, .const 0]

def addCarryCompileContext : CompileContext (RiscV.Word 64) :=
  { vars := [("result", (.comb [.one, .one], [0, 1]))]
    functions := []
    exceptions := []
    maxVar := 1
    bytesInWord := 8 }

def addCarryLoopContext : LoopContext (RiscV.Word 64) :=
  { vars := []
    functions := []
    maxVar := 1
    target := .rv64i }

def addCarryCompiledLoop : LoopProg (RiscV.Word 64) :=
  loopCompileProg addCarryLoopContext []
    (compileProg addCarryCompileContext addCarrySource)

example :
    (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
      addCarrySourceLocals (fun _ => none) (fun _ => none)
      RiscV.panPrimitiveHandler addCarrySource).map
        (fun result =>
          match result.1 "result" with
          | some (.rStruct [.word left, .word carry]) =>
              (some left, some carry)
          | _ => (none, none)) =
      (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 20
        { locals := fun _ => none, globals := fun _ => none,
          memory := fun _ => none } addCarryCompiledLoop).map
        (fun result => ((loopResultState result).locals 0,
          (loopResultState result).locals 1)) := by
  native_decide

example :
    (evalLoopProg 10 loopSharedMemoryTestState
      (.seq
        (.shMem .store 2 (.var 1))
        (.shMem .load 3 (.var 1)))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 42) := by
  native_decide

example :
    (evalLoopFfi loopFfiTestHandler 10 loopFfiTestState
      (.ffi "sum" 1 2 3 4 [])).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  native_decide

example :
    (evalLoopProgWithCallsAndFfi
      [(7, [1], (.return [1] : LoopProg Nat))]
      loopFfiTestHandler 20 loopFfiTestState
      (.seq
        (.call (some ([6], [])) (some 7) [1] none)
        (.ffi "sum" 1 2 3 4 []))).map (fun result =>
        match result with
        | .normal state => state.locals 5
        | _ => none) = some (some 33) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(7, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 7) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(8, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call none (some 8) [1] none)).map loopResultValues = some [9] := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(9, [1], (.raise 1 : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 9) [1]
        (some (4, .assign 3 (.var 4), .skip, [])))).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(10, [1],
          (.seq
            (.call (some ([2], [])) (some 11) [1] none)
            (.return [2]) : LoopProg Nat)),
       (11, [1], (.return [1] : LoopProg Nat))] 10 loopCallTestState
      (.call (some ([3], [])) (some 10) [1] none)).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    (evalLoopProgWithFunctions
      [(12, [1], (.return [1] : LoopProg Nat))] 20 loopCallTestState
      (.loop []
        (.seq
          (.call (some ([3], [])) (some 12) [1] none)
          (.break 0)) [])).map (fun result =>
        match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 9) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.while (.const (BitVec.ofNat 64 0)) .break)
            (.return (.const (BitVec.ofNat 64 7))), returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 7] := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq
            (.store (.const (BitVec.ofNat 64 100))
              (.const (BitVec.ofNat 64 42)))
            (.return (.load .one (.const (BitVec.ofNat 64 100)))),
          returnShape := .one }]
    (result.functions[0]?).bind (fun (_, _, artifact) =>
      artifact.bind (fun (code, returns) =>
        RiscV.executeFunction 200 (0 : RiscV.Word 64) [] code returns []
          (RiscV.zeroState 64))) = some [BitVec.ofNat 64 42] := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .ite (.cmp .equal (.const (BitVec.ofNat 64 1))
            (.const (BitVec.ofNat 64 1)))
            (.return (.const (BitVec.ofNat 64 7)))
            (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    let result := compileFlapjackRiscV (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]
    result.functions.length = 1 &&
      result.functions.all (fun (_, _, artifact) => artifact.isSome) := by
  native_decide

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  native_decide

example :
    staticResultOk (compileFlapjackChecked (α := Nat) .rv64i 1 id
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  native_decide

example :
    let result := compileFlapjack (α := Nat) .rv64i 1 id
      [.decl .one "g" (.const 7), .function
        { name := "main", inline := false, exported := true, params := [],
          body := .return (.var .global "g"), returnShape := .one }]
    result.globals.initializers.length = 1 ∧ result.crepe.length = 1 := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineExceptionCodes,
    pipelineFunctionInfos, pipelineLoopFunctions, pipelineLoopFunctionsAux,
    pipelineWordFunctions, pipelinePrependInitializers,
    compileToCrepe, compileFunctions, compileFunDecl, compileParamVars,
    compileProg, loopCompileProg, loopCompileExp, loopCompileExp.loopCompileExps,
    loopCompileExps, loopNestedSeq, loopTempNames, wordFindVar, lookupInfo,
    lookupNatInfo]

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 7), returnShape := .one }]) = true := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.rStruct []), returnShape := .one }]) = false := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }]) = false := by
  native_decide

example :
    (staticCheck (α := Nat)
      [.function
        { name := "main", inline := false, exported := false, params := [],
          body := .seq (.return (.const 7)) .skip, returnShape := .one }]).2.length = 1 := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one },
       .function
        { name := "f", inline := false, exported := false, params := [],
          body := .return (.const 1), returnShape := .one }]) = false := by
  native_decide

example :
    staticResultOk (staticCheck (α := Nat)
      [.decl .one "g" (.rStruct []), .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one }]) = false := by
  native_decide

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsl (.var 2) (.var 3)) =
      some (.sll 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .lsr (.var 2) (.var 3)) =
      some (.srl 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .asr (.var 2) (.var 3)) =
      some (.sra 1 2 3) := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example [NeZero width] :
    RiscV.wordExpToInstruction (width := width) 1
      (.shift .ror (.var 2) (.var 3)) = none := by
  simp [RiscV.wordExpToInstruction, RiscV.registerOfNat]

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) =
      some [.srli 31 2 3, .slli 1 2 5, .or 1 1 31] := by
  native_decide

example :
    RiscV.wordExpToInstructions (width := 8) 1
      (.shift .ror (.var 2) (.var 3)) =
      some [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] := by
  native_decide

example :
    RiscV.wordExpToInstructions (width := 8) 31
      (.shift .ror (.var 2) (.const (3 : RiscV.Word 8))) = none := by
  native_decide

example :
    RiscV.executeFunction 20 (0 : RiscV.Word 8) [2]
      [.srli 31 2 1, .slli 1 2 7, .or 1 1 31] [1]
      [129] (RiscV.zeroState 8) = some [192] := by
  native_decide

example :
    RiscV.executeFunction 30 (0 : RiscV.Word 8) [2, 3]
      [.ori 31 0 8, .sub 31 31 3, .sll 31 2 31,
        .srl 1 2 3, .or 1 1 31] [1]
      [129, 1] (RiscV.zeroState 8) = some [192] := by
  native_decide

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.var 3))) =
      some (RiscV.execute state (.sll 1 2 3)) := by
  exact RiscV.compileWordShiftLsl_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.var 3))) =
      some (RiscV.execute state (.srl 1 2 3)) := by
  exact RiscV.compileWordShiftLsr_sound state

example [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.var 3))) =
      some (RiscV.execute state (.sra 1 2 3)) := by
  exact RiscV.compileWordShiftAsr_sound state

example :
    RiscV.shiftAmount (BitVec.ofNat 64 65) = 1 := by
  native_decide

example :
    evalPanExp (fun _ => none)
      (.panOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  native_decide

example :
    evalCrepExp (fun _ => none)
      (.crepOp .mul [.const (α := Nat) 6, .const 7]) = some 42 := by
  native_decide

example :
    evalCrepProg (fun _ => none)
        (compileProg crepContext
          (.return (.panOp .mul [.const (α := Nat) 6, .const 7]))) =
      evalPanProg (fun _ => none)
        (.return (.panOp .mul [.const (α := Nat) 6, .const 7])) := by
  exact compile_pan_mul_const_preserves_semantics crepContext 6 7
    (fun _ => none) (fun _ => none)

def emptyLoopState : LoopState Nat :=
  { locals := fun _ => none, globals := fun _ => none, memory := fun _ => none }

def loopDivisionState : LoopState Nat :=
  { locals := fun name =>
      if name = 1 then some 42 else if name = 2 then some 6 else none
    globals := fun _ => none, memory := fun _ => none }

example :
    (evalLoopProg 10 loopDivisionState
      (.seq (.arith (.div 3 1 2)) (.return [3]))).map loopResultValues =
      some [7] := by
  native_decide

example :
    (evalLoopProg 1 loopDivisionState (.arith (.div 3 1 2))).map
      (fun result => match result with
        | .normal state => state.locals 3
        | _ => none) = some (some 7) := by
  native_decide

example :
    (evalLoopProg 1
      { loopDivisionState with locals := fun name =>
          if name = 1 then some 42 else if name = 2 then some 0 else none }
      (.arith (.div 3 1 2))).isNone = true := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .add [.const 6, .crepOp .mul [.const 5, .const 6]]) = some 36 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .sub [.const 9, .const 4]) = some 5 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .and [.const 13, .const 6]) = some 4 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .or [.const 8, .const 3]) = some 11 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.op .xor [.const 13, .const 6]) = some 11 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsl (.const 3) (.const 2)) = some 12 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.shift .lsr (.const 13) (.const 2)) = some 3 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.cmp .lower (.const 3) (.const 5)) = some 1 := by
  native_decide

example :
    evalLoopExp emptyLoopState
      (.cmp .notLower (.const 5) (.const 3)) = some 1 := by
  native_decide

example : evalLoopCondition .less (3 : Nat) 5 = some true := by
  native_decide

example : evalLoopCondition .notLess (5 : Nat) 3 = some true := by
  native_decide

example : evalLoopCondition .test (5 : Nat) 2 = some true := by
  native_decide

example : evalLoopCondition .notTest (5 : Nat) 1 = some true := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .less (.const (3 : Nat)) (.const 5)) =
    some 1 := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .test (.const (5 : Nat)) (.const 2)) =
    some 1 := by
  native_decide

example : evalLoopExp emptyLoopState (.cmp .notTest (.const (5 : Nat)) (.const 1)) =
    some 1 := by
  native_decide

example :
    (evalLoopProg 10 emptyLoopState
      (.seq (.assign 0 (.const 42)) (.return [0]))).map loopResultValues =
      some [42] := by
  native_decide

example :
    evalLoopProg 1 emptyLoopState (.break 7) =
      some (.broke emptyLoopState 7) := by
  exact evalLoopProg_break emptyLoopState 7

example :
    evalLoopProg 1 emptyLoopState (.continue 8) =
      some (.continued emptyLoopState 8) := by
  exact evalLoopProg_continue emptyLoopState 8

example :
    evalLoopProg 1 emptyLoopState (.tick) =
      some (.normal emptyLoopState) := by
  exact evalLoopProg_tick emptyLoopState

example :
    (evalLoopProg 10 emptyLoopState
      (.loop [] (.break 0) [])).map loopResultValues = some [] := by
  native_decide

example :
    (evalLoopProg 12 emptyLoopState
      (loopCompileProg loopContext [] (.return [(.const (α := Nat) 7)]))).map
        loopResultValues = some [7] := by
  exact evalLoopCompile_return_const loopContext [] emptyLoopState 7

example :
    Option.map loopResultValues
      (evalLoopProg 20 emptyLoopState
      (loopCompileProg loopContext []
          (.return [(.crepOp .mul [.const (α := Nat) 6, .const 7])]))) =
      some [42] := by
  native_decide

example :
    evalPanCondition (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.cmp .equal (.var .local "x") (.const 7)) = some true := by
  native_decide

example :
    evalPanProg (α := Nat)
        (fun name => if name == "x" then some 7 else none)
        (.ite (.cmp .equal (.var .local "x") (.const 7))
          (.return (.const 1)) (.return (.const 0))) = some [1] := by
  native_decide

example :
    (evalPanMemProgFuel 4
      (fun _ => none)
      (fun address => if address == 4 then some 7 else none)
      (.ite (.cmp .equal (.load .one (.const 4)) (.const 7))
        (.return (.const 1)) (.return (.const 0)))).map
      (fun result => result.2.2) = some [1] := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .sub [.const 9, .const 4]) = some 5 := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .and [.const 5, .const 3]) = some 1 := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.op .xor [.const 5, .const 3]) = some 6 := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.cmp .lower (.const 3) (.const 5)) = some 1 := by
  native_decide

example :
    evalPanCondition (α := Nat) (fun _ => none)
      (.cmp .notLower (.const 5) (.const 3)) = some true := by
  native_decide

example :
    evalPanExp (α := Nat) (fun _ => none)
      (.shift .lsl (.const 3) (.const 2)) = some 12 := by
  native_decide

example :
    evalPanValueExp (α := Nat) []
      (fun _ => none) (fun _ => none) (fun _ => none) 0 100 8
      (.rField 1 (.rStruct [.const 3, .const 5])) = some (.word 5) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]

end Flapjack
