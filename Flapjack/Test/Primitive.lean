import Flapjack.Pipeline
import Flapjack.RiscV.PanSemantics

namespace Flapjack

def primitivePipelineDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .dec "result" (.comb [.one, .one])
        (.rStruct [.const 0, .const 0])
        (.seq
          (.primitive "result" .addCarry
            [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
              .const (BitVec.ofNat 64 0)])
          (.return (.rField 0 (.var .local "result")))),
      returnShape := .one }]

def primitivePipeline :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    primitivePipelineDeclarations

def primitivePipelineRun : Option (List (RiscV.Word 64)) :=
  match primitivePipeline.functions with
  | [(_, parameters, some (code, returns))] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 200 0 parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def primitivePipelineCallLinkedRun : Option (List (RiscV.Word 64)) :=
  match primitivePipeline.callLinkedFunctions with
  | some [(_, _, parameters, code, returns)] =>
      let returnAddress := BitVec.ofNat 64 (4 * code.length)
      RiscV.executeFunctionAt 300 0 0 returnAddress
        (parameters.mapM RiscV.registerOfNat |>.getD []) code returns []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 returnAddress)
  | _ => none

def primitivePipelineSource : Prog (RiscV.Word 64) :=
  .dec "result" (.comb [.one, .one])
    (.rStruct [.const 0, .const 0])
    (.seq
      (.primitive "result" .addCarry
        [.const 1, .const 2, .const 0])
      (.return (.rField 0 (.var .local "result"))))

theorem primitivePipeline_source_correct :
    (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
      (fun _ => none) (fun _ => none) (fun _ => none)
      RiscV.panPrimitiveHandler primitivePipelineSource).map
        (fun result =>
          match result.2.2.2 with
          | [.word value] => some value
          | _ => none) =
      some (some (BitVec.ofNat 64 3)) := by
  native_decide

theorem primitivePipeline_correct :
    primitivePipelineRun =
      (evalPanValueProgWithPrimitive (α := RiscV.Word 64) [] 0 100 8
        (fun _ => none) (fun _ => none) (fun _ => none)
        RiscV.panPrimitiveHandler primitivePipelineSource).map
        (fun result =>
          match result.2.2.2 with
          | [.word value] => [value]
          | _ => []) := by
  native_decide

theorem primitivePipeline_call_link_correct :
    primitivePipelineCallLinkedRun = some [BitVec.ofNat 64 3] := by
  native_decide

end Flapjack
