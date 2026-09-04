import Flapjack.Pipeline
import Flapjack.Semantics
import Flapjack.LoopSemantics
import Flapjack.RiscV.Backend

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

end Flapjack
