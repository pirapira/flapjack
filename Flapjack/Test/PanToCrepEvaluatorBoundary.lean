import Flapjack.Pancake.Proofs.PanToCrep.EvaluatorBoundary

/-! Kernel-checked examples for every control constructor in the concrete
Pan-to-Crep evaluator result boundary. -/

namespace Flapjack.Test.PanToCrepEvaluatorBoundary

variable {α σ : Type}

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    panToCrepControlResultRel context
      (.control (.normal locals globals memory ffi)) .normal := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    panToCrepControlResultRel context
      (.timeout locals globals memory ffi) .timeout := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) :
    panToCrepControlResultRel context
      (.control (.returned locals globals memory ffi values))
      (.returned (values.flatMap panValueFlatten)) := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α) (code : α)
    (hcode : FLOOKUP context.eids exception = some code) :
    panToCrepControlResultRel context
      (.control (.raised locals globals memory ffi exception value))
      (.raised code) := by
  exact hcode

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    panToCrepControlResultRel context
      (.control (.broke locals globals memory ffi)) (.broke 0) := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    panToCrepControlResultRel context
      (.control (.continued locals globals memory ffi)) (.continued 0) := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (event : FfiFinalEvent) :
    panToCrepControlResultRel context
      (.control (.finalFfi locals globals memory ffi event)) (.finalFfi event) := by
  simp [panToCrepControlResultRel]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) (state : CrepRuntimeState α σ)
    (hclock : state.clock = clock) :
    panToCrepRunResultRel context
      (some (.control (.normal locals globals memory ffi), clock))
      (some (.normal, state)) := by
  simp [panToCrepRunResultRel, panToCrepControlResultRel, hclock]

example [BEq String] (context : PanToCrepProofContext α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    ¬ panToCrepControlResultRel context
      (.control (.normal locals globals memory ffi)) .error := by
  simp [panToCrepControlResultRel]

end Flapjack.Test.PanToCrepEvaluatorBoundary
