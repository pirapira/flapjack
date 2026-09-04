import Flapjack.Pipeline
import Flapjack.Semantics
import Flapjack.LoopSemantics
import Flapjack.RiscV.Backend
import Flapjack.WordSemantics

/-!
Initial end-to-end correctness theorem for the executable Flapjack pipeline.

This module deliberately starts with a small, fully parameterized RV64
function. It connects the source Pancake evaluator to the artifact emitted by
the complete front-end/Loop/Word/RISC-V composition; larger simulation
relations can be added beside this theorem as more instructions and states are
ported.
-/

namespace Flapjack

def pipelineAddDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "add", inline := false, exported := false,
      params := [("left", .one), ("right", .one)],
      body := .return (.op .add
        [.var .local "left", .var .local "right"]), returnShape := .one }]

def pipelineAddPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineAddDeclarations

def pipelineAddFunctions := pipelineAddPipeline.functions

def pipelineAddLinkedFunctions := pipelineAddPipeline.linkedFunctions

theorem pipelineAddFunctions_shape :
    pipelineAddFunctions =
      [(1, [2, 3], some ([.add 5 2 3], [5]))] := by
  native_decide

theorem pipelineAddLinkedFunctions_shape :
    pipelineAddLinkedFunctions =
      some [(1, 0, [2, 3], [.add 5 2 3], [5])] := by
  change RiscV.linkRiscVFunctions 0 pipelineAddFunctions = _
  rw [pipelineAddFunctions_shape]
  rfl

def compiledPipelineAddRun (left right : RiscV.Word 64) :
    Option (List (RiscV.Word 64)) :=
  match pipelineAddLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns
            [left, right] (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineAddSource (left right : RiscV.Word 64) : Prog (RiscV.Word 64) :=
  .return (.op .add [.var .local "left", .var .local "right"])

def pipelineAddLocals (left right : RiscV.Word 64) :
    VarName → Option (RiscV.Word 64) :=
  fun name => if name == "left" then some left
    else if name == "right" then some right else none

theorem compiledPipelineAdd_correct (left right : RiscV.Word 64) :
    compiledPipelineAddRun left right =
      evalPanProg (pipelineAddLocals left right) (pipelineAddSource left right) := by
  simp [compiledPipelineAddRun, pipelineAddLinkedFunctions_shape,
    pipelineAddSource, pipelineAddLocals, evalPanProg, evalPanExp]
  exact RiscV.executeFunction_add_general left right

def pipelineMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := false, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)]),
      returnShape := .one }]

def pipelineMulPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineMulDeclarations

def pipelineMulLinkedFunctions := pipelineMulPipeline.linkedFunctions

theorem pipelineMulFunctions_shape :
    pipelineMulPipeline.functions =
      [(1, [], some ([.addi 3 0 (BitVec.ofNat 64 2),
        .addi 4 0 (BitVec.ofNat 64 3), .mulHU 5 3 4, .mul 5 3 4,
        .addi 6 5 0], [6]))] := by
  native_decide

theorem pipelineMulLinkedFunctions_shape :
    pipelineMulLinkedFunctions =
      some [(1, 0, [],
        [.addi 3 0 (BitVec.ofNat 64 2), .addi 4 0 (BitVec.ofNat 64 3),
          .mulHU 5 3 4, .mul 5 3 4, .addi 6 5 0], [6])] := by
  change RiscV.linkRiscVFunctions 0 pipelineMulPipeline.functions = _
  rw [pipelineMulFunctions_shape]
  rfl

def compiledPipelineMulRun : Option (List (RiscV.Word 64)) :=
  match pipelineMulLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineMulSource : Prog (RiscV.Word 64) :=
  .return (.panOp .mul
    [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)])

theorem compiledPipelineMul_correct :
    compiledPipelineMulRun =
      evalPanProg (fun _ => none) pipelineMulSource := by
  native_decide

/-!
The first end-to-end call regression. The source program uses a declaration
call rather than an unbound low-level call, so the static front end allocates
the result local and the call-aware linker can recover the callee's return
layout. The concrete image also checks the ordinary-call link register
save/restore sequence.
-/
def pipelineCallDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "result")), returnShape := .one }]

def pipelineCallPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineCallDeclarations

theorem pipelineCallLinkedFunctions_available :
    pipelineCallPipeline.callLinkedFunctions.isSome := by
  native_decide

def pipelineCallImage : List (RiscV.Instruction 64) :=
  [.addi 4 2 0, .jalr 0 1 0,
   .addi 3 0 0, .addi 4 0 (BitVec.ofNat 64 41),
   .addi 2 4 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
   .storeWord 1 30, .addi 31 0 0, .jalr 1 31 0,
   .addi 3 4 0, .loadWord 1 30,
   .addi 30 30 (BitVec.ofNat 64 8), .addi 4 3 0,
   .jalr 0 1 0]

theorem pipelineCall_word_semantics :
    (do
      let (_, main) ←
        RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
      let (_, values) ←
        RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
          30 (RiscV.zeroState 64) main
      pure values) = some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCall_compiled_execution :
    RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
      pipelineCallImage [4] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 100) =
      some [BitVec.ofNat 64 41] := by
  native_decide

def pipelineCallSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def pipelineCallSourceMain : Prog (RiscV.Word 64) :=
  .decCall "result" .one "id"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "result"))

theorem pipelineCall_source_semantics :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
      some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCall_source_word_machine_agreement :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let (_, main) ←
          RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
        let (_, values) ←
          RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
            30 (RiscV.zeroState 64) main
        pure values) = some [BitVec.ofNat 64 41] ∧
      RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
        pipelineCallImage [4] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 100) =
        some [BitVec.ofNat 64 41] := by
  exact ⟨pipelineCall_source_semantics, pipelineCall_word_semantics,
    pipelineCall_compiled_execution⟩

/-!
The first compositional bridge between the Loop and Word semantic states.
Only the destination register is observed here; the full state relation will
add globals, memory, live-register preservation, and control results as the
remaining Word operations are ported.
-/
def loopRegisterState [NeZero width] (state : RiscV.State width) :
    LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat name).map (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMapped [NeZero width] (context : WordContext)
    (state : RiscV.State width) : LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat (wordFindVar context name)).map
        (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMappedWithMemory [NeZero width] (context : WordContext)
    (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width)) :
    LoopState (RiscV.Word width) :=
  { loopRegisterStateMapped context state with memory := memory }

/-!
This is the first context-parametric Loop-to-Word state observation. The
source local and its mapped register need not have the same numeric name; the
only required premise is that the mapped destination is a valid RISC-V
register. It is the base case needed before extending the relation to
expression evaluation and sequencing.
-/
theorem loopToWord_const_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination : Nat) (value : RiscV.Word width) (register : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hregister :
      RiscV.registerOfNat (wordFindVar context destination) = some register)
    (hregister_nonzero : register ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.const value)))).map
        (fun state => RiscV.readRegister state register) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterStateMapped,
    loopToWordProg, wordCompileExp, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, hregister, hregister_nonzero, hzero]

theorem loopToWord_add_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination left right : Nat) (destinationRegister leftRegister rightRegister : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hleft :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.op .add [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op .add [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp,
    loopRegisterStateMapped, loopToWordProg, wordCompileExp,
    wordCompileExp.wordCompileExpList,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
    RiscV.nextPc, updateLoopLocal, hdestination, hleft, hright,
    hdestination_nonzero, hzero]

theorem loopToWord_load32_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory : memory addressValue = some value)
    (hmachine : RiscV.readWord32 state addressValue = value)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.load32 address destination)).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.load32 address destination))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, wordCompileExp,
    RiscV.evalWordProg, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, haddress_value,
    hmemory, hmachine, hdestination_nonzero, hzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmemory, hmachine]
  simp [updateLoopLocal]

theorem loopToWord_const_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state)
    (value : RiscV.Word width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.const value)))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterState, loopToWordProg, loopToWordExp,
    wordCompileExp, wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal, hzero]

theorem loopToWord_add_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.op .add [.var 2, .var 3]))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.op .add [.var 2, .var 3])))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp, loopRegisterState,
    loopToWordProg, wordCompileExp, wordCompileExp.wordCompileExpList,
    wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal, hzero]

theorem loopToWord_longMul_register_agreement [NeZero width]
    (state : RiscV.State width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.arith (.longMul 1 1 2 3))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.arith (.longMul 1 1 2 3)))).map
        (fun state => RiscV.readRegister state 1) := by
  simp [evalLoopProg, loopRegisterState, loopToWordProg, wordArith,
    wordFindVar, lookupNatInfo, RiscV.evalWordProg,
    RiscV.wordArithToInstructions, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal]

end Flapjack
