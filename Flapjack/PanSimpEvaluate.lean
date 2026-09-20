import Flapjack.PanSimp
import Flapjack.PanEvaluate
import Flapjack.PanValueFfiClockFuel

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
end Flapjack
