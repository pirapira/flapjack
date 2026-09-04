import Flapjack.Pipeline
import Flapjack.Semantics
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

end Flapjack
