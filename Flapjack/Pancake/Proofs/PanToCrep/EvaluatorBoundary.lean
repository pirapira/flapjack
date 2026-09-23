import Flapjack.Semantics
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanSem

namespace Flapjack

/-! The source compatibility evaluator keeps a list-backed function table,
while the production Crep evaluator now reads its HOL-shaped finite code map
directly from `CrepRuntimeState.code`. These relations connect the source
lookup table and a proof caller's target map to those actual evaluator
boundaries. The source projection retains parameter names and bodies; shape
metadata is checked by `codeRel` itself. -/
def panSourceRuntimeCodeRel [BEq String]
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (runtimeFunctions : List (FunName × List VarName × Prog α)) : Prop :=
  ∀ function variableShapes program returnShape,
    FLOOKUP sourceCode function = some (variableShapes, program, returnShape) →
      lookupPanFunction function runtimeFunctions =
        some (variableShapes.map Prod.fst, program)

def crepRuntimeCodeRel
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (targetState : CrepRuntimeState α σ) : Prop :=
  targetState.code = targetCode

/-- Relate HOL's finite-map code assumption to the exact lookup tables used by
the shipped clocked source evaluator and target Crep evaluator. -/
def panToCrepRuntimeCodeRel [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ) : Prop :=
  codeRel context sourceCode targetCode ∧
    panSourceRuntimeCodeRel sourceCode sourceState.legacy.functions ∧
    crepRuntimeCodeRel targetCode targetState

/-! These wrappers expose the production evaluators directly.  In particular,
there is no evaluator callback parameter that could replace either semantics. -/
def panToCrepSourceEvaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateExactState context primitive handler state program

def panToCrepTargetEvaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (handler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) (program : Prog α) :
    Option (CrepRuntimeStep α σ FfiFinalEvent) :=
  evalCrepRuntimeResult handler primitive fuel state
    (compileCodeRelProg context program)

/-! Successful control-result correspondence needed by the case split in HOL
`pc_compile_correct`.  The source clock evaluator uses outer `none` for
evaluation errors, whereas HOL distinguishes `NONE` from `SOME Error`; this
boundary therefore covers successful `some` runs only.  A missing
exception-code entry has no matching raised result, as in HOL's
`NONE => F` exception branch. -/
def panToCrepControlResultRel [BEq String]
    (context : PanToCrepProofContext α)
    (source : PanValueFfiClockOutcome α σ)
    (target : CrepRuntimeResult α FfiFinalEvent) : Prop :=
  match source, target with
  | .timeout _ _ _ _, .timeout => True
  | .control (.normal _ _ _ _), .normal => True
  | .control (.returned _ _ _ _ values), .returned words =>
      words = values.flatMap panValueFlatten
  | .control (.raised _ _ _ _ exception _), .raised code =>
      FLOOKUP context.eids exception = some code
  | .control (.broke _ _ _ _), .broke 0 => True
  | .control (.continued _ _ _ _), .continued 0 => True
  | .control (.finalFfi _ _ _ _ event), .finalFfi targetEvent =>
      event = targetEvent
  | _, _ => False

def panToCrepRunResultRel [BEq String]
    (context : PanToCrepProofContext α)
    (source : Option (PanValueFfiClockResult α σ))
    (target : Option (CrepRuntimeStep α σ FfiFinalEvent)) : Prop :=
  match source, target with
  | some (outcome, sourceClock), some (result, targetState) =>
      sourceClock = targetState.clock ∧
        panToCrepControlResultRel context outcome result
  | _, _ => False

/-! This is the concrete evaluator simulation goal for the later proof slice.
The code relation premise covers Call lookup on both runtime representations;
the target execution is an existential conclusion, never an input premise. The
result relation currently covers successful control constructors and clock;
the final state, locals relation, and raised-payload globals obligations remain
part of the later `pc_compile_correct` induction, so this definition is not
itself a correctness theorem. -/
def panToCrepConcreteEvaluationGoal
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ) (program : Prog α) : Prop :=
  panToCrepRuntimeCodeRel context sourceCode targetCode sourceState targetState →
    ∀ sourceRun,
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState program = some sourceRun →
      ∃ targetRun,
        panToCrepTargetEvaluate context targetHandler targetPrimitive fuel
          targetState program = targetRun ∧
        panToCrepRunResultRel context (some sourceRun) targetRun


end Flapjack
