import Flapjack.CrepeProgramRelation

/-!
Inversion of the source evaluator for local assignment.

The source assignment rule evaluates its right-hand side, checks that the
result preserves the destination shape, and then updates the existing local.
This lemma packages those facts so program-level correctness proofs can work
from a successful source evaluation without unfolding that evaluator at every
use site.
-/

namespace Flapjack

theorem evalPanValueProg_assign_local_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (name : VarName) (expression : Exp α)
    (sourceResult : PanValueControlResult α)
    (hsource : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name expression) = some sourceResult) :
    ∃ value oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some value ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs value)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name value)
        sourceGlobals sourceMemory := by
  cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression with
  | none =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
  | some value =>
      cases hlocal : sourceLocals name with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            panValueAssignmentValid, hvalue, hlocal] at hsource
      | some oldValue =>
          cases hvalid : panShapeMatches (panValueShape structs value)
              (panValueShape structs oldValue) with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                panValueAssignmentValid, hvalue, hlocal, hvalid] at hsource
          | true =>
              have hresult : sourceResult =
                  .normal (updatePanValueMap sourceLocals name value)
                    sourceGlobals sourceMemory := by
                exact (Option.some.inj (by
                  simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                    panValueAssignmentValid, hvalue, hlocal, hvalid] using hsource)).symm
              exact ⟨value, oldValue, by simp, by simp,
                hvalid, hresult⟩

end Flapjack
