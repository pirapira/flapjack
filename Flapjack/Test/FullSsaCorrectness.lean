import Flapjack.Test.FullSsaPipeline

namespace Flapjack

/-! Named correctness boundary for the complete full-SSA declaration-call
    slice.  The source side reduces through the call evaluator in the kernel;
    the linked RISC-V execution is kept as a native-decision theorem because
    the image crosses the kernel reduction boundary documented by the
    repository's native-decision policy. -/

theorem fullSsaCall_source_execution :
    (evalPanProgWithCalls fullSsaCallSourceFunctions 20 (fun _ => none)
      fullSsaCallSourceMain).map (fun result => result.2) =
      some [BitVec.ofNat 64 41] := by
  simp [fullSsaCallSourceMain, fullSsaCallSourceFunctions,
    evalPanProgWithCalls, evalPanCallWithCalls, evalPanExps,
    evalPanExp, lookupPanFunction, bindPanParameters, updatePanLocal]

theorem fullSsaCall_machine_execution :
    fullSsaCallMachineResult = some [BitVec.ofNat 64 41] := by
  native_decide

theorem fullSsaCall_source_machine_agreement :
    (evalPanProgWithCalls fullSsaCallSourceFunctions 20 (fun _ => none)
      fullSsaCallSourceMain).map (fun result => result.2) =
      some [BitVec.ofNat 64 41] ∧
    fullSsaCallMachineResult = some [BitVec.ofNat 64 41] := by
  exact ⟨fullSsaCall_source_execution, fullSsaCall_machine_execution⟩

/-! The direct source-to-machine equation is the simulation interface for
    clients that only need the observable result of the complete full-SSA FFI
    path, while the call theorem above keeps its source and machine checks
    independently inspectable. -/

theorem fullSsaFfi_source_machine_simulation :
    (evalPanProgWithCallsAndFfi [] fullSsaFfiSourceHandler 20
      (fun _ => none) fullSsaFfiMainBody).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) =
      (do
        let image ← fullSsaFfiImage
        RiscV.executeFunctionAtWithFfi fullSsaFfiHost 100 0 76 42 [] image [2] []
          (RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 42))) := by
  calc
    _ = some [BitVec.ofNat 64 42] := fullSsaFfi_source_execution
    _ = _ := fullSsaFfi_compiled_execution.symm

end Flapjack
