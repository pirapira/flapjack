import Flapjack.PanSimp
import Flapjack.PanEvaluate

/-!
# Evaluator-level `pan_simp` obligations

CakeML's `pan_simpProofScript.sml` proves the semantic correctness of the
`pan_simp` pass on top of the `panSem$evaluate` equations.  The first
building blocks are the `Skip`/sequencing absorption rules
(`evaluate_seq_skip`, `evaluate_skip_seq`) and the body-equivalence rule for
`While` (`evaluate_while_body_same`).

The Lean clocked evaluator `evalPanValueFfiClockProg` consumes one unit of
fuel per `Seq` node, so the counterparts below keep the successor fuel
explicit; the state and clock equations are otherwise the same as the
source.  These are proof-only: no compiler code changes.
-/

namespace Flapjack

theorem evalPanValueFfiClockLeaf_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockLeaf context primitive handler structs functions
        baseAddress topAddress bytesInWord clock locals globals memory ffi
        (.skip : Prog α) (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- Clocked counterpart of Cake's `evaluate_seq_skip`
    (`pan_simpProofScript.sml:46-50`): a trailing `Skip` is absorbed. -/
theorem evalPanValueFfiClockProg_seq_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq program .skip) (memoryAccess := memoryAccess)
        (contracts := contracts) (memoryHandler := memoryHandler) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi
        clock program (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) := by
  cases fuel with
  | zero => simp [evalPanValueFfiClockProg]
  | succ f =>
      cases h : evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord (f + 1) locals globals memory ffi
          clock program (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) with
      | none => simp [evalPanValueFfiClockProg, h]
      | some result =>
          rw [evalPanValueFfiClockProg, h]
          obtain ⟨outcome, resultClock⟩ := result
          cases outcome with
          | control r =>
              cases r <;>
                simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf_skip]
          | timeout _ _ _ _ => simp

/-- Clocked counterpart of Cake's `evaluate_skip_seq`
    (`pan_simpProofScript.sml:52-54`): a leading `Skip` is absorbed. -/
theorem evalPanValueFfiClockProg_skip_seq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq .skip program) (memoryAccess := memoryAccess)
        (contracts := contracts) (memoryHandler := memoryHandler) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi
        clock program (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) := by
  cases fuel with
  | zero => simp [evalPanValueFfiClockProg]
  | succ f =>
      simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf_skip]

end Flapjack
