import Flapjack.PanSimp
import Flapjack.PanEvaluate
import Flapjack.PanValueFfiClockFuel
import Flapjack.PanValueFfiClockCorrectness

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

/-! A small structural fragment used by the fuel-adequacy proof.  It contains
    only `Skip` and sequencing, so its additive structural bound is independent
    of the source clock and of runtime calls or loops. -/
def panSimpSkipSeqProg : Prog α → Prop
  | .skip => True
  | .seq first second => panSimpSkipSeqProg first ∧ panSimpSkipSeqProg second
  | _ => False

def panSimpSkipSeqFuel : Prog α → Nat
  | .skip => 1
  | .seq first second =>
      1 + panSimpSkipSeqFuel first + panSimpSkipSeqFuel second
  | _ => 0

theorem panSimpSkipSeqProg_seqAssoc (pre : Prog α) (program : Prog α)
    (hpre : panSimpSkipSeqProg pre)
    (hprogram : panSimpSkipSeqProg program) :
    panSimpSkipSeqProg (seqAssoc pre program) := by
  let rec go (pre : Prog α) : (program : Prog α) →
      panSimpSkipSeqProg pre → panSimpSkipSeqProg program →
      panSimpSkipSeqProg (seqAssoc pre program)
    | .skip, hpre, _ => by simpa [seqAssoc] using hpre
    | .seq first second, hpre, hprogram => by
        simp only [seqAssoc]
        exact go (seqAssoc pre first) second
          (go pre first hpre hprogram.1) hprogram.2
    | .dec _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .assign _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .primitive _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .store _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .store32 _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .storeByte _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .ite _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .while _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .break, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .continue, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .call _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .decCall _ _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .extCall _ _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .raise _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .return _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .shMemLoad _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .shMemStore _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .tick, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .annot _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre program hpre hprogram

theorem panSimpSkipSeqFuel_seqAssoc_le (pre : Prog α) (program : Prog α)
    (hpre : panSimpSkipSeqProg pre)
    (hprogram : panSimpSkipSeqProg program) :
    panSimpSkipSeqFuel (seqAssoc pre program) ≤
      panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program := by
  let rec go (pre : Prog α) : (program : Prog α) →
      panSimpSkipSeqProg pre → panSimpSkipSeqProg program →
      panSimpSkipSeqFuel (seqAssoc pre program) ≤
        panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program
    | .skip, hpre, _ => by simp [seqAssoc, panSimpSkipSeqFuel]
    | .seq first second, hpre, hprogram => by
        simp only [seqAssoc, panSimpSkipSeqFuel]
        have hfirst := go pre first hpre hprogram.1
        have hsecond := go (seqAssoc pre first) second
          (panSimpSkipSeqProg_seqAssoc pre first hpre hprogram.1) hprogram.2
        omega
    | .dec _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .assign _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .primitive _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .store _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .store32 _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .storeByte _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .ite _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .while _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .break, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .continue, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .call _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .decCall _ _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .extCall _ _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .raise _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .return _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .shMemLoad _ _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .shMemStore _ _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .tick, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    | .annot _ _, _, hprogram => by simp [panSimpSkipSeqProg] at hprogram
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre program hpre hprogram

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

/-- Clocked counterpart of Cake's `evaluate_while_body_same`
    (`pan_simpProofScript.sml:59-74`): if two loop bodies agree on every state,
    so do the loops.  Each iteration consumes one unit of fuel, so the Lean
    proof is a strong induction on fuel rather than on the clock. -/
theorem evalPanValueFfiClockProg_while_body_same
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (condition : Exp α) (body body' : Prog α)
    (hbody : ∀ (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (ffi : FfiState σ)
        (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
        (mh : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock body
        (memoryAccess := ma) (contracts := c) (memoryHandler := mh) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock body'
        (memoryAccess := ma) (contracts := c) (memoryHandler := mh)) :
    ∀ (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)
      (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
      (mh : Option (PanValueMemoryFfiHandler α σ)),
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        (.while condition body) (memoryAccess := ma) (contracts := c)
        (memoryHandler := mh) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        (.while condition body') (memoryAccess := ma) (contracts := c)
        (memoryHandler := mh) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro clock locals globals memory ffi ma c mh
    cases fuel with
    | zero => simp [evalPanValueFfiClockProg]
    | succ f =>
      simp only [evalPanValueFfiClockProg]
      cases hc : evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord condition ma with
      | none => rfl
      | some cv =>
        cases cv with
        | word w =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          by_cases hz : (w == 0) = true
          · simp [hz]
          · simp only [if_neg hz]
            by_cases hclock : (clock == 0) = true
            · simp [hclock]
            · simp only [if_neg hclock]
              rw [hbody f (clock - 1) locals globals memory ffi ma c mh]
              have hloop : ∀ (cl : Nat) (l g : VarName → Option (PanValue α))
                  (m : α → Option (PanValue α)) (ff : FfiState σ),
                  evalPanValueFfiClockProg context primitive handler structs functions
                    baseAddress topAddress bytesInWord f l g m ff cl (.while condition body)
                    ma c mh =
                  evalPanValueFfiClockProg context primitive handler structs functions
                    baseAddress topAddress bytesInWord f l g m ff cl (.while condition body')
                    ma c mh :=
                fun cl l g m ff => ih f (by omega) cl l g m ff ma c mh
              simp only [hloop]
        | rStruct fields => simp
        | nStruct nm fields => simp

/-! Clocked counterpart of Cake's `evaluate_while_no_error_imp`
    (`pan_simpProofScript.sml:89-103`).  When the condition is a nonzero word,
    the clock is nonzero, and the loop succeeds, the body evaluator cannot
    have returned an error (`none`). -/
theorem evalPanValueFfiClockProg_while_some_implies_body_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (condition : Exp α) (body : Prog α)
    (fuel clock : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (conditionValue : α)
    (hcondition : evalPanValueExp structs locals globals memory
      baseAddress topAddress bytesInWord condition
      (memoryAccess := memoryAccess) = some (.word conditionValue))
    (hconditionNonzero : (conditionValue == 0) = false)
    (hclockNonzero : (clock == 0) = false)
    (result : PanValueFfiClockResult α σ)
    (hresult : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.while condition body) (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) = some result) :
    ∃ bodyResult,
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi
        (decPanClock clock) body (memoryAccess := memoryAccess)
        (contracts := contracts) (memoryHandler := memoryHandler) = some bodyResult := by
  cases hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (decPanClock clock) body (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) with
  | none =>
      simp [evalPanValueFfiClockProg, hcondition, hconditionNonzero,
        hclockNonzero, hbody] at hresult
  | some bodyResult =>
      exact ⟨bodyResult, rfl⟩

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

/-- Clocked counterpart of Cake's `evaluate_seq_no_error_fst`
    (`pan_simpProofScript.sml:149-155`): an error-free `Seq` has an
    error-free first component.  Errors are represented by `none`. -/
theorem evalPanValueFfiClockProg_seq_no_none
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
    (first second : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (h : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first second) ma c mh ≠ none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      first ma c mh ≠ none := by
  intro hfirst
  apply h
  simp [evalPanValueFfiClockProg, hfirst]

/-- Clocked counterpart of Cake's `evaluate_while_no_error_imp`
    (`pan_simpProofScript.sml:112-121`): a non-timeout, error-free `While`
    whose condition is a non-zero word has an error-free body. -/
theorem evalPanValueFfiClockProg_while_no_none
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
    (condition : Exp α) (body : Prog α) (w : α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hcond : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord condition ma = some (.word w))
    (hw : ¬(w == 0) = true)
    (hclock : ¬(clock == 0) = true)
    (h : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.while condition body) ma c mh ≠ none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi
      (clock - 1) body ma c mh ≠ none := by
  intro hbody
  apply h
  simp [evalPanValueFfiClockProg, hcond, hw, hclock, hbody]

/-- Congruence of the clocked evaluator under the first component of a `Seq`.
    This is the fuel-compatible building block needed to reassociate sequences:
    a `Seq` at `fuel + 1` evaluates its first component at `fuel`, so replacing
    that component by an evaluation-equal one leaves the whole `Seq` equal. -/
theorem evalPanValueFfiClockProg_seq_congr
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
    (first first' second : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (h : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        first ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        first' ma c mh) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first second) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first' second) ma c mh := by
  simp only [evalPanValueFfiClockProg]
  rw [h]

/-! Contrapositive of fuel monotonicity: a run that fails at a larger fuel also
    fails at every smaller fuel.  This is the missing direction needed to line
    up two runs whose structural fuel budgets differ, as happens for
    `seqAssoc` (which inserts/removes `Seq` nodes) under the fuel-indexed
    clocked evaluator. -/
theorem evalPanValueFfiClockProg_fuel_anti
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuel fuel' : Nat} (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hfuel : fuel ≤ fuel')
    (hnone : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock program
      ma c mh = none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh = none := by
  cases h : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh with
  | none => rfl
  | some result =>
      have hmono := evalPanValueFfiClockProg_fuel_mono context primitive handler
        structs functions baseAddress topAddress bytesInWord locals globals memory ffi
        clock program ma c mh hfuel h
      rw [hnone] at hmono
      simp at hmono
/-! A sound replacement for fixed-fuel evaluator equalities.  The two programs
    may need different structural fuel budgets; once both have successful
    results at their respective budgets, fuel monotonicity transports both
    results to a common upper budget. -/
theorem evalPanValueFfiClockProg_eq_of_common_fuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuelLeft fuelRight commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (programLeft programRight : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hleft : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelLeft locals globals memory ffi clock
      programLeft ma c mh = some result)
    (hright : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelRight locals globals memory ffi clock
      programRight ma c mh = some result)
    (hleftFuel : fuelLeft ≤ commonFuel)
    (hrightFuel : fuelRight ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      programLeft ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      programRight ma c mh := by
  have hleftCommon := evalPanValueFfiClockProg_fuel_mono context primitive handler
    structs functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    programLeft ma c mh hleftFuel hleft
  have hrightCommon := evalPanValueFfiClockProg_fuel_mono context primitive handler
    structs functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    programRight ma c mh hrightFuel hright
  rw [hleftCommon, hrightCommon]

/-! Cake's `evaluate_seq_assoc` compares the source sequence with its
    right-associated `seqAssoc` form.  The clocked evaluator additionally
    needs successful runs at possibly different structural fuel budgets; this
    source-shaped wrapper exposes that obligation without weakening it. -/
theorem evalPanValueFfiClockProg_seqAssoc_eq_of_common_fuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (pre program : Prog α)
    {fuelLeft fuelRight commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hleft : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelLeft locals globals memory ffi clock
      (seqAssoc pre program) ma c mh = some result)
    (hright : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelRight locals globals memory ffi clock
      (.seq pre program) ma c mh = some result)
    (hleftFuel : fuelLeft ≤ commonFuel)
    (hrightFuel : fuelRight ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (seqAssoc pre program) ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (.seq pre program) ma c mh := by
  exact evalPanValueFfiClockProg_eq_of_common_fuel context primitive handler structs
    functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    (seqAssoc pre program) (.seq pre program) ma c mh hleft hright hleftFuel
    hrightFuel

/-! Clocked counterpart of Cake's `ret_to_tail_correct` at a common fuel.  The
    transformed and source programs retain the same explicit result premise;
    only the fuel transport is abstracted by the upward-closed bridge. -/
theorem evalPanValueFfiClockProg_retToTail_eq_of_common_fuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α)
    {fuelTail fuelSource commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (htail : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelTail locals globals memory ffi clock
      (retToTail program) ma c mh = some result)
    (hsource : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelSource locals globals memory ffi clock
      program ma c mh = some result)
    (htailFuel : fuelTail ≤ commonFuel)
    (hsourceFuel : fuelSource ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (retToTail program) ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      program ma c mh := by
  exact evalPanValueFfiClockProg_eq_of_common_fuel context primitive handler structs
    functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    (retToTail program) program ma c mh htail hsource htailFuel hsourceFuel

/-! Top-level clocked counterpart of Cake's `compile_correct_same_state` pass
    boundary.  `panSimpProg` is the composed `seqAssoc`/`retToTail` transform;
    both successful source-shaped results and their fuel bounds stay explicit. -/
theorem evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α)
    {fuelCompiled fuelSource commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hcompiled : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelCompiled locals globals memory ffi clock
      (panSimpProg program) ma c mh = some result)
    (hsource : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelSource locals globals memory ffi clock
      (seqAssoc (.skip : Prog α) program) ma c mh = some result)
    (hcompiledFuel : fuelCompiled ≤ commonFuel)
    (hsourceFuel : fuelSource ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (panSimpProg program) ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (seqAssoc (.skip : Prog α) program) ma c mh := by
  exact evalPanValueFfiClockProg_retToTail_eq_of_common_fuel context primitive handler
    structs functions baseAddress topAddress bytesInWord
    (seqAssoc (.skip : Prog α) program) (fuelTail := fuelCompiled)
    (fuelSource := fuelSource) (commonFuel := commonFuel) locals globals memory ffi clock
    ma c mh hcompiled hsource hcompiledFuel hsourceFuel

/-! Direct source-shaped form of Cake's `compile_correct_same_state`.  The
    clocked evaluator needs a separate successful run for the intermediate
    `seqAssoc Skip` program: its structural fuel can differ from the original
    program even though the Cake clock is unchanged.  Keeping that run and its
    fuel bound explicit gives a faithful theorem without asserting a false
    fixed-fuel equality. -/
theorem evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel_source
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α)
    {fuelCompiled fuelAssoc fuelSource commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hcompiled : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelCompiled locals globals memory ffi clock
      (panSimpProg program) ma c mh = some result)
    (hassoc : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelAssoc locals globals memory ffi clock
      (seqAssoc (.skip : Prog α) program) ma c mh = some result)
    (hsource : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelSource locals globals memory ffi clock
      program ma c mh = some result)
    (hcompiledFuel : fuelCompiled ≤ commonFuel)
    (hassocFuel : fuelAssoc ≤ commonFuel)
    (hsourceFuel : fuelSource ≤ commonFuel)
    (hsourceSeqFuel : fuelSource + 1 ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (panSimpProg program) ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      program ma c mh := by
  have hcompiledAssoc := evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel
    context primitive handler structs functions baseAddress topAddress bytesInWord
    program (fuelCompiled := fuelCompiled) (fuelSource := fuelAssoc)
    (commonFuel := commonFuel) locals globals memory ffi clock ma c mh
    hcompiled hassoc hcompiledFuel hassocFuel
  have hsourceSeq : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuelSource + 1) locals globals memory ffi clock
      (.seq (.skip : Prog α) program) ma c mh = some result := by
    rw [evalPanValueFfiClockProg_skip_seq context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelSource clock locals globals memory ffi
      program ma c mh]
    exact hsource
  have hassocSource := evalPanValueFfiClockProg_seqAssoc_eq_of_common_fuel
    context primitive handler structs functions baseAddress topAddress bytesInWord
    (.skip : Prog α) program (fuelLeft := fuelAssoc) (fuelRight := fuelSource + 1)
    (commonFuel := commonFuel) locals globals memory ffi clock ma c mh
    hassoc hsourceSeq hassocFuel hsourceSeqFuel
  have hsourceCommon := evalPanValueFfiClockProg_fuel_mono context primitive handler
    structs functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    program ma c mh hsourceFuel hsource
  have hsourceSeqCommon := evalPanValueFfiClockProg_fuel_mono context primitive handler
    structs functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    (.seq (.skip : Prog α) program) ma c mh hsourceSeqFuel hsourceSeq
  have hseqSource : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (.seq (.skip : Prog α) program) ma c mh =
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      program ma c mh := by
    rw [hsourceSeqCommon, hsourceCommon]
  exact hcompiledAssoc.trans (hassocSource.trans hseqSource)

/-! Successful-run form of the source-shaped `compile_correct_same_state`
    bridge.  Consumers that need the transformed result, rather than an
    equality between two common-fuel runs, can retain the source result and
    transport it without hiding any of the three fuel bounds. -/
theorem evalPanValueFfiClockProg_panSimpProg_result_of_common_fuel_source
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α)
    {fuelCompiled fuelAssoc fuelSource commonFuel : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hcompiled : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelCompiled locals globals memory ffi clock
      (panSimpProg program) ma c mh = some result)
    (hassoc : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelAssoc locals globals memory ffi clock
      (seqAssoc (.skip : Prog α) program) ma c mh = some result)
    (hsource : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuelSource locals globals memory ffi clock
      program ma c mh = some result)
    (hcompiledFuel : fuelCompiled ≤ commonFuel)
    (hassocFuel : fuelAssoc ≤ commonFuel)
    (hsourceFuel : fuelSource ≤ commonFuel)
    (hsourceSeqFuel : fuelSource + 1 ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord commonFuel locals globals memory ffi clock
      (panSimpProg program) ma c mh = some result := by
  have heq := evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel_source
    context primitive handler structs functions baseAddress topAddress bytesInWord
    program (fuelCompiled := fuelCompiled) (fuelAssoc := fuelAssoc)
    (fuelSource := fuelSource) (commonFuel := commonFuel) locals globals memory ffi
    clock ma c mh hcompiled hassoc hsource hcompiledFuel hassocFuel hsourceFuel
    hsourceSeqFuel
  have hsourceCommon := evalPanValueFfiClockProg_fuel_mono context primitive handler
    structs functions baseAddress topAddress bytesInWord locals globals memory ffi clock
    program ma c mh hsourceFuel hsource
  rw [heq, hsourceCommon]

/-! Congruence under the second component of a `Seq`.  The premise is
    quantified over the post-first state and clock because the first component
    may update every evaluator component before the second starts. -/
theorem evalPanValueFfiClockProg_seq_congr_second
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
    (first second second' : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hsecond : ∀ (fuel clock : Nat)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ),
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        second ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        second' ma c mh) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first second) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.seq first second') ma c mh := by
  simp only [evalPanValueFfiClockProg]
  cases hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first ma c mh with
  | none => simp
  | some firstResult =>
      obtain ⟨firstOutcome, firstClock⟩ := firstResult
      cases firstOutcome with
      | control firstControl =>
          cases firstControl with
          | normal nextLocals nextGlobals nextMemory nextFfi =>
              simp only [Option.bind_eq_bind, Option.bind_some]
              rw [hsecond fuel firstClock nextLocals nextGlobals nextMemory nextFfi]
          | _ => simp
      | timeout nextLocals nextGlobals nextMemory nextFfi => simp

/-! A normal result from a `Seq` exposes the intermediate normal state and the
    second component's evaluation.  This is the clocked state/result case used
    when lifting Cake's sequence equations through the source evaluator. -/
theorem evalPanValueFfiClockProg_seq_normal_some_implies_components_some
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
    (first second : Prog α)
    (finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (finalClock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hresult : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.seq first second) ma c mh =
      some (.control (.normal finalLocals finalGlobals finalMemory finalFfi), finalClock)) :
    ∃ (middleLocals middleGlobals : VarName → Option (PanValue α))
      (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
      (middleClock : Nat),
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        first ma c mh =
        some (.control (.normal middleLocals middleGlobals middleMemory middleFfi),
          middleClock) ∧
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel middleLocals middleGlobals
        middleMemory middleFfi middleClock second ma c mh =
        some (.control (.normal finalLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp only [evalPanValueFfiClockProg] at hresult
  cases hfirst : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first ma c mh with
  | none => simp [hfirst] at hresult
  | some firstResult =>
      obtain ⟨firstOutcome, middleClock⟩ := firstResult
      cases firstOutcome with
      | control firstControl =>
          cases firstControl with
          | normal middleLocals middleGlobals middleMemory middleFfi =>
              rw [hfirst] at hresult
              simp only [Option.bind_eq_bind, Option.bind_some] at hresult
              exact ⟨middleLocals, middleGlobals, middleMemory, middleFfi,
                middleClock, rfl, hresult⟩
          | _ => simp [hfirst] at hresult
      | timeout nextLocals nextGlobals nextMemory nextFfi => simp [hfirst] at hresult

/-- Concrete demonstration that `seqAssoc` is **not** fuel-preserving under the
    fuel-indexed clocked evaluator.  For `p = Seq Skip (Seq Skip Skip)`, at
    fuel `2` the transformed program `seqAssoc .skip p` evaluates to a normal
    result while the source `Seq .skip p` times out (`none`).  Hence no
    fixed-fuel analogue of Cake's `evaluate_seq_assoc` (which holds because
    Cake's `Seq` does not consume clock) can be stated; the port must use a
    fuel-adequacy / upward-closed-success formulation instead. -/
theorem evalPanValueFfiClockProg_seqAssoc_fuel_gap
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord 2 locals globals memory ffi clock
        (seqAssoc (.skip : Prog α) (.seq .skip (.seq .skip .skip))) =
      some (.control (.normal locals globals memory ffi), clock) ∧
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord 2 locals globals memory ffi clock
        (.seq .skip (.seq .skip .skip)) = none := by
  constructor <;>
    simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf_skip, seqAssoc]

/-- The leaf evaluation of `Return (Var .local name)` reduces to the singleton
    `.returned` of the local's value, retaining the caller's globals, memory,
    FFI state and clock.  This is the read-back half of the `pan_simp`
    tail-call fusion. -/
theorem evalPanValueFfiClockLeaf_return_var
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
    (name : VarName) (value : PanValue α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hlookup : locals name = some value)
    (hwithin : panValuePayloadWithinLimit structs value = true) :
    evalPanValueFfiClockLeaf context primitive handler structs functions
        baseAddress topAddress bytesInWord clock locals globals memory ffi
        (.return (.var .local name)) ma c mh =
      some (.control (.returned (fun _ => none) globals memory ffi [value]), clock) := by
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, evalPanValueExpCounted,
    evalPanValueExp, hlookup, hwithin]

/-- Fusion of the `pan_simp` tail-call pattern.  When a call whose return value
    is stored in local `returnName` returns normally, the sequence
    `Call ... ; Return (Var returnName)` evaluates to exactly the `.returned`
    result of the tail call `Call none ...`: the destination read-back supplies
    the returned value.  This is the clocked, fuel-aware analogue of Cake's
    `evaluate_seq_call_ret_eq`, stated with explicit successful-run premises
    (the call result and the destination lookup) rather than a fixed-fuel
    equality. -/
theorem evalPanValueFfiClockProg_seq_call_return_returned
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock callClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName) (arguments : List (Exp α))
    (returnName returnedName : VarName) (value : PanValue α)
    (assignedLocals assignedGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hcall : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
      (some (some (.local, returnName), none)) function arguments ma c mh =
      some (.control (.normal assignedLocals assignedGlobals nextMemory nextFfi),
        callClock))
    (hlookup : assignedLocals returnedName = some value)
    (hwithin : panValuePayloadWithinLimit structs value = true) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 2) locals globals memory ffi
        clock (.seq (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnedName))) ma c mh =
      some (.control (.returned (fun _ => none) assignedGlobals nextMemory nextFfi
        [value]), callClock) := by
  simp only [evalPanValueFfiClockProg]
  rw [hcall]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact evalPanValueFfiClockLeaf_return_var context primitive handler structs functions
    baseAddress topAddress bytesInWord callClock assignedLocals assignedGlobals
    nextMemory nextFfi returnedName value ma c mh hlookup hwithin

/-- The `seqCallRet` tail-call fusion in the direction Cake uses.  If the
    destination call `Call (SOME (SOME (Local, returnName), NONE)) ...` returns
    normally from a body that itself `return`s `[value]`, then the tail call
    `Call NONE ...` and the original sequence
    `Call ... ; Return (Var returnName)` agree at the same structural fuel.
    This is the clocked analogue of Cake's `evaluate_seq_call_ret_eq` with an
    explicit successful-run premise instead of a fixed-fuel equality. -/
theorem evalPanValueFfiClockProg_seq_call_return_tail_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock finalClock : Nat) (hclock : clock ≠ 0)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (value : PanValue α) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (returnName : VarName) (assignedLocals : VarName → Option (PanValue α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (hargs : evalPanValueExps structs locals globals memory baseAddress topAddress
      bytesInWord arguments (memoryAccess := memoryAccess) = some [value])
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters [value] = some calleeLocals)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi
      (clock - 1) body (memoryAccess := memoryAccess) (contracts := none)
      (memoryHandler := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi [value]),
        finalClock))
    (hwithin : panValueValuesWithinLimit structs [value] = true)
    (hpayload : panValuePayloadWithinLimit structs value = true)
    (hassign : assignPanValueCallResult locals finalGlobals (some (.local, returnName))
      [value] (structs := structs) = some (assignedLocals, finalGlobals))
    (hlookupReturn : assignedLocals returnName = some value) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 3) locals globals memory ffi
        clock (.call none function arguments) (memoryAccess := memoryAccess)
        (contracts := none) (memoryHandler := none) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 3) locals globals memory ffi
        clock (.seq (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnName))) (memoryAccess := memoryAccess)
        (contracts := none) (memoryHandler := none) := by
  have hbodyFuel : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) calleeLocals globals memory ffi
      (clock - 1) body (memoryAccess := memoryAccess) (contracts := none)
      (memoryHandler := none) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi [value]),
        finalClock) :=
    evalPanValueFfiClockProg_fuel_mono context primitive handler structs functions
      baseAddress topAddress bytesInWord (locals := calleeLocals) (globals := globals)
      (memory := memory) (ffi := ffi) (clock := clock - 1) (program := body)
      (ma := memoryAccess) (c := none) (mh := none) (by omega) hbody
  have hL : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 3) locals globals memory ffi
      clock (.call none function arguments) (memoryAccess := memoryAccess)
      (contracts := none) (memoryHandler := none) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi
        [value]), finalClock) := by
    simp only [evalPanValueFfiClockProg]
    exact evalPanValueFfiClockCall_returned_no_destination context primitive handler
      structs functions baseAddress topAddress bytesInWord (fuel + 1) clock finalClock
      locals globals memory ffi [value] parameters calleeLocals bodyLocals
      finalGlobals finalMemory finalFfi body function arguments memoryAccess
      hargs hlookup hbind hclock hbodyFuel hwithin
  have hR : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 3) locals globals memory ffi
      clock (.seq (.call (some (some (.local, returnName), none)) function arguments)
        (.return (.var .local returnName))) (memoryAccess := memoryAccess)
      (contracts := none) (memoryHandler := none) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi
        [value]), finalClock) := by
    simp only [evalPanValueFfiClockProg]
    rw [evalPanValueFfiClockCall_returned_destination context primitive handler structs
      functions baseAddress topAddress bytesInWord fuel clock finalClock locals
      globals memory ffi [value] parameters calleeLocals bodyLocals finalGlobals
      finalMemory finalFfi body function arguments (some (.local, returnName))
      assignedLocals finalGlobals memoryAccess hargs hlookup hbind hclock hbody hwithin
      hassign]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact evalPanValueFfiClockLeaf_return_var context primitive handler structs functions
      baseAddress topAddress bytesInWord finalClock assignedLocals finalGlobals
      finalMemory finalFfi returnName value memoryAccess none none hlookupReturn hpayload
  rw [hL, hR]

/-- Syntactic shape of the `seqCallRet` tail-call rewrite, used to connect the
    evaluator fusion above to the `pan_simp` pass itself. -/
theorem seqCallRet_tail_call (returnName : VarName) (function : FunName)
    (arguments : List (Exp α)) :
    seqCallRet (.seq (.call (some (some (.local, returnName), none)) function arguments)
      (.return (.var .local returnName))) = .call none function arguments := by
  simp [seqCallRet]

/-! ## Fuel adequacy for the `Skip`/`Seq` fragment

Cake's `evaluate_seq_assoc` holds at a fixed clock because `Seq` does not
consume clock.  The clocked evaluator instead spends one unit of structural
fuel per `Seq` node, so the port must bound the fuel by the shape of the
program.  On the smallest fragment -- programs built only from `Skip` and
`Seq` -- evaluation always succeeds, and the explicit structural budget below
makes both the transformed and the source shape produce the same normal
result.  The remaining general cases (leaf constructors that may fail) are
recorded on bead `flapjack-pxn.11`.
-/

inductive PanSimpSeqSkipFragment : Prog α → Prop
  | skip : PanSimpSeqSkipFragment (.skip : Prog α)
  | seq (first second : Prog α) :
      PanSimpSeqSkipFragment first → PanSimpSeqSkipFragment second →
      PanSimpSeqSkipFragment (.seq first second)

def panSimpSeqSkipFuel : Prog α → Nat
  | .skip => 1
  | .seq first second =>
      max (panSimpSeqSkipFuel first) (panSimpSeqSkipFuel second) + 1
  | _ => 0

theorem panSimpSeqSkipFuel_le_sizeOf {program : Prog α}
    (hfrag : PanSimpSeqSkipFragment program) :
    panSimpSeqSkipFuel program ≤ sizeOf program := by
  induction hfrag with
  | skip => simp [panSimpSeqSkipFuel]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [panSimpSeqSkipFuel]
      have hsize : sizeOf (Prog.seq first second) =
          1 + sizeOf first + sizeOf second := rfl
      omega

theorem evalPanValueFfiClockProg_seqSkipFragment_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hfrag : PanSimpSeqSkipFragment program)
    (hfuel : panSimpSeqSkipFuel program ≤ fuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        program ma c mh =
      some (.control (.normal locals globals memory ffi), clock) := by
  induction hfrag generalizing fuel locals globals memory ffi clock with
  | skip =>
      cases fuel with
      | zero => simp [panSimpSeqSkipFuel] at hfuel
      | succ f =>
          simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf_skip]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      cases fuel with
      | zero => simp [panSimpSeqSkipFuel] at hfuel
      | succ f =>
          have hf1 : panSimpSeqSkipFuel first ≤ f := by
            simp only [panSimpSeqSkipFuel] at hfuel; omega
          have hf2 : panSimpSeqSkipFuel second ≤ f := by
            simp only [panSimpSeqSkipFuel] at hfuel; omega
          simp only [evalPanValueFfiClockProg]
          rw [ihfirst f locals globals memory ffi clock hf1]
          simp only [Option.bind_eq_bind, Option.bind_some]
          exact ihsecond f locals globals memory ffi clock hf2

/-- `seqAssoc` preserves the `Skip`/`Seq` fragment. -/
theorem PanSimpSeqSkipFragment_seqAssoc {program : Prog α}
    (hfrag : PanSimpSeqSkipFragment program) :
    ∀ pre, PanSimpSeqSkipFragment pre →
      PanSimpSeqSkipFragment (seqAssoc pre program) := by
  induction hfrag with
  | skip =>
      intro pre hpre
      rw [seqAssoc.eq_1]
      exact hpre
  | seq first second hfirst hsecond ihfirst ihsecond =>
      intro pre hpre
      rw [seqAssoc.eq_3]
      exact ihsecond (seqAssoc pre first) (ihfirst pre hpre)

/-- Cake's `evaluate_seq_assoc` for the `Skip`/`Seq` fragment under the clocked
    evaluator: both sides are fuel-adequate once the common budget dominates the
    structural budgets of the reassociated and source shapes, and on this
    fragment they reduce to the same normal result. -/
theorem evalPanValueFfiClockProg_seqAssoc_eq_of_seqSkipFragment
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (pre program : Prog α)
    (commonFuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hpre : PanSimpSeqSkipFragment pre)
    (hprogram : PanSimpSeqSkipFragment program)
    (hleftFuel : panSimpSeqSkipFuel (seqAssoc pre program) ≤ commonFuel)
    (hrightFuel : panSimpSeqSkipFuel (.seq pre program) ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord commonFuel locals globals memory ffi
        clock (seqAssoc pre program) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord commonFuel locals globals memory ffi
        clock (.seq pre program) ma c mh := by
  rw [evalPanValueFfiClockProg_seqSkipFragment_some context primitive handler structs
        functions baseAddress topAddress bytesInWord commonFuel locals globals
        memory ffi clock (seqAssoc pre program) ma c mh
        (PanSimpSeqSkipFragment_seqAssoc hprogram pre hpre) hleftFuel,
      evalPanValueFfiClockProg_seqSkipFragment_some context primitive handler structs
        functions baseAddress topAddress bytesInWord commonFuel locals globals
        memory ffi clock (.seq pre program) ma c mh
        (.seq pre program hpre hprogram) hrightFuel]


/-! ## Bridging the additive foundation to the evaluator corollary

`panSimpSkipSeqProg`/`panSimpSkipSeqFuel` (the additive structural budget) and
`PanSimpSeqSkipFragment`/`panSimpSeqSkipFuel` (the max-based budget) describe the
same `Skip`/`Seq` fragment.  The bridges below let the additive foundation feed
the evaluator-level `seqAssoc` corollary. -/

theorem panSimpSeqSkipFragment_of_skipSeqProg {program : Prog α}
    (h : panSimpSkipSeqProg program) : PanSimpSeqSkipFragment program := by
  let rec go : (program : Prog α) → panSimpSkipSeqProg program →
      PanSimpSeqSkipFragment program
    | .skip, _ => .skip
    | .seq first second, h => .seq first second (go first h.1) (go second h.2)
    | .dec _ _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .assign _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .primitive _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .store _ _, h => by simp [panSimpSkipSeqProg] at h
    | .store32 _ _, h => by simp [panSimpSkipSeqProg] at h
    | .storeByte _ _, h => by simp [panSimpSkipSeqProg] at h
    | .ite _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .while _ _, h => by simp [panSimpSkipSeqProg] at h
    | .break, h => by simp [panSimpSkipSeqProg] at h
    | .continue, h => by simp [panSimpSkipSeqProg] at h
    | .call _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .decCall _ _ _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .extCall _ _ _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .raise _ _, h => by simp [panSimpSkipSeqProg] at h
    | .return _, h => by simp [panSimpSkipSeqProg] at h
    | .shMemLoad _ _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .shMemStore _ _ _, h => by simp [panSimpSkipSeqProg] at h
    | .tick, h => by simp [panSimpSkipSeqProg] at h
    | .annot _ _, h => by simp [panSimpSkipSeqProg] at h
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program h

theorem panSimpSkipSeqProg_of_fragment {program : Prog α}
    (h : PanSimpSeqSkipFragment program) : panSimpSkipSeqProg program := by
  induction h with
  | skip => trivial
  | seq first second hfirst hsecond ihfirst ihsecond => exact ⟨ihfirst, ihsecond⟩

theorem panSimpSeqSkipFuel_le_skipSeqFuel {program : Prog α}
    (h : PanSimpSeqSkipFragment program) :
    panSimpSeqSkipFuel program ≤ panSimpSkipSeqFuel program := by
  induction h with
  | skip => simp [panSimpSeqSkipFuel, panSimpSkipSeqFuel]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [panSimpSeqSkipFuel, panSimpSkipSeqFuel]
      have hmax1 := Nat.le_max_left (panSimpSeqSkipFuel first)
        (panSimpSeqSkipFuel second)
      have hmax2 := Nat.le_max_right (panSimpSeqSkipFuel first)
        (panSimpSeqSkipFuel second)
      omega

/-- Evaluator-level Cake `evaluate_seq_assoc` corollary stated directly on the
    additive foundation: the common budget
    `panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program + 1` dominates both
    shapes' structural budgets, so the reassociated and source programs agree. -/
theorem evalPanValueFfiClockProg_seqAssoc_eq_of_skipSeqProg
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (pre program : Prog α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hpre : panSimpSkipSeqProg pre)
    (hprogram : panSimpSkipSeqProg program) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord
        (panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program + 1)
        locals globals memory ffi clock (seqAssoc pre program) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord
        (panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program + 1)
        locals globals memory ffi clock (.seq pre program) ma c mh := by
  apply evalPanValueFfiClockProg_seqAssoc_eq_of_seqSkipFragment
    context primitive handler structs functions baseAddress topAddress bytesInWord
    pre program (panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program + 1)
    locals globals memory ffi clock ma c mh
    (panSimpSeqSkipFragment_of_skipSeqProg hpre)
    (panSimpSeqSkipFragment_of_skipSeqProg hprogram)
  · have hbridge := panSimpSeqSkipFuel_le_skipSeqFuel
      (PanSimpSeqSkipFragment_seqAssoc
        (panSimpSeqSkipFragment_of_skipSeqProg hprogram) pre
        (panSimpSeqSkipFragment_of_skipSeqProg hpre))
    have hadd := panSimpSkipSeqFuel_seqAssoc_le pre program hpre hprogram
    omega
  · simp only [panSimpSeqSkipFuel]
    have hb1 := panSimpSeqSkipFuel_le_skipSeqFuel
      (panSimpSeqSkipFragment_of_skipSeqProg hpre)
    have hb2 := panSimpSeqSkipFuel_le_skipSeqFuel
      (panSimpSeqSkipFragment_of_skipSeqProg hprogram)
    omega

/-! ## `retToTail` on the `Skip`/`Seq` fragment

`retToTail` only rewrites `Call`/`Return` tail-call shapes, so on the
`Skip`/`Seq` fragment it is the identity.  Consequently the full `pan_simp`
program transform `panSimpProg = retToTail (seqAssoc .skip)` collapses to the
sequence reassociation on the fragment, and Cake's `compile_correct_same_state`
holds there with the same structural fuel budget. -/

theorem PanSimpSeqSkipFragment_retToTail {program : Prog α}
    (hfrag : PanSimpSeqSkipFragment program) : retToTail program = program := by
  induction hfrag with
  | skip => simp [retToTail]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      rw [retToTail.eq_3, ihfirst, ihsecond]
      cases hfirst <;> simp [seqCallRet]

theorem evalPanValueFfiClockProg_retToTail_eq_of_seqSkipFragment
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hprogram : PanSimpSeqSkipFragment program) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        (retToTail program) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        program ma c mh := by
  rw [PanSimpSeqSkipFragment_retToTail hprogram]

theorem evalPanValueFfiClockProg_panSimpProg_eq_of_seqSkipFragment
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (program : Prog α) (commonFuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hprogram : PanSimpSeqSkipFragment program)
    (hcompiledFuel : panSimpSeqSkipFuel (panSimpProg program) ≤ commonFuel)
    (hsourceFuel : panSimpSeqSkipFuel program ≤ commonFuel) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord commonFuel locals globals memory ffi
        clock (panSimpProg program) ma c mh =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord commonFuel locals globals memory ffi
        clock program ma c mh := by
  have hseq : PanSimpSeqSkipFragment (seqAssoc (.skip : Prog α) program) :=
    PanSimpSeqSkipFragment_seqAssoc hprogram (.skip : Prog α)
      PanSimpSeqSkipFragment.skip
  have hid : retToTail (seqAssoc (.skip : Prog α) program) =
      seqAssoc (.skip : Prog α) program :=
    PanSimpSeqSkipFragment_retToTail hseq
  simp only [panSimpProg] at hcompiledFuel ⊢
  rw [hid] at hcompiledFuel ⊢
  rw [evalPanValueFfiClockProg_seqSkipFragment_some context primitive handler structs
        functions baseAddress topAddress bytesInWord commonFuel locals globals memory
        ffi clock (seqAssoc (.skip : Prog α) program) ma c mh hseq hcompiledFuel,
      evalPanValueFfiClockProg_seqSkipFragment_some context primitive handler structs
        functions baseAddress topAddress bytesInWord commonFuel locals globals memory
        ffi clock program ma c mh hprogram hsourceFuel]

/-! ## Per-constructor success equations for the clocked evaluator

These are the success-premise building blocks the general fuel-adequacy
framework needs for the constructors whose leaf/recursive clauses were not yet
covered: `Annot` and `Tick` (clock-preserving / clock-consuming leaves), `Seq`
composition, and the terminating `While` with a zero condition.  Each keeps the
source locals, globals, memory and FFI state visible. -/

theorem evalPanValueFfiClockLeaf_annot
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
    (tag text : String)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockLeaf context primitive handler structs functions
        baseAddress topAddress bytesInWord clock locals globals memory ffi
        (.annot tag text) ma c mh =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

theorem evalPanValueFfiClockProg_annot_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (tag text : String)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.annot tag text) ma c mh =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf_annot]

theorem evalPanValueFfiClockProg_tick_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (hclock : clock ≠ 0) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
        clock (.tick : Prog α) ma c mh =
      some (.control (.normal locals globals memory ffi), decPanClock clock) := by
  simp [evalPanValueFfiClockProg, hclock]

theorem evalPanValueFfiClockProg_seq_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (first second : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (nextLocals nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ) (nextClock : Nat)
    (result : PanValueFfiClockOutcome α σ) (resultClock : Nat)
    (hfirst : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        first ma c mh = some (.control (.normal nextLocals nextGlobals nextMemory nextFfi),
          nextClock))
    (hsecond : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
        nextClock second ma c mh = some (result, resultClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.seq first second) ma c mh = some (result, resultClock) := by
  simp [evalPanValueFfiClockProg, hfirst, hsecond]

theorem evalPanValueFfiClockProg_while_zero_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (condition : Exp α) (body : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (w : α)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord condition (memoryAccess := ma) = some (.word w))
    (hw : (w == 0) = true) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.while condition body) ma c mh =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, hcondition, hw]

/-! ### Declaration and conditional success equations

These are the first non-`Skip`/`Seq` constructors: `Dec` binds the evaluated
value, checks the shape, runs the body, and restores the shadowed local;
`Ite` selects a branch on a nonzero word condition.  Both keep the source
locals/globals/memory/FFI state and the explicit clock visible. -/

theorem evalPanValueFfiClockProg_dec_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (valueResult : PanValue α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord value (memoryAccess := ma) = some valueResult)
    (hmatch : panShapeMatches (panValueShape structs valueResult) shape = true)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel
        (updatePanValueMap locals name valueResult) globals memory ffi clock body
        (memoryAccess := ma) (contracts := c) (memoryHandler := mh) =
      some (outcome, nextClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.dec name shape value body) (memoryAccess := ma) (contracts := c)
        (memoryHandler := mh) =
      some (panValueFfiClockRestoreLocal name (locals name) outcome, nextClock) := by
  simp [evalPanValueFfiClockProg, hvalue, hmatch, hbody]

theorem evalPanValueFfiClockProg_ite_true_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (wordValue : α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord condition (memoryAccess := ma) = some (.word wordValue))
    (hnonzero : (wordValue != 0) = true)
    (hthen : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        thenBranch (memoryAccess := ma) (contracts := c) (memoryHandler := mh) =
      some (outcome, nextClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.ite condition thenBranch elseBranch) (memoryAccess := ma) (contracts := c)
        (memoryHandler := mh) =
      some (outcome, nextClock) := by
  simp [evalPanValueFfiClockProg, hcondition, hnonzero, hthen]

theorem evalPanValueFfiClockProg_ite_false_some
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (wordValue : α)
    (outcome : PanValueFfiClockOutcome α σ) (nextClock : Nat)
    (hcondition : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord condition (memoryAccess := ma) = some (.word wordValue))
    (hzero : (wordValue != 0) = false)
    (helse : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        elseBranch (memoryAccess := ma) (contracts := c) (memoryHandler := mh) =
      some (outcome, nextClock)) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
        (.ite condition thenBranch elseBranch) (memoryAccess := ma) (contracts := c)
        (memoryHandler := mh) =
      some (outcome, nextClock) := by
  simp [evalPanValueFfiClockProg, hcondition, hzero, helse]

end Flapjack
