import Flapjack.PanValueFfiClockSemantics

/-!
# Fuel monotonicity for the clocked stateful-FFI evaluators

The clocked half of issue #659. The unclocked evaluators are covered by
`Flapjack.PanValueFfiFuel` in PR #662; this file is independent of it, and
states the same thing for the explicit-clock evaluators of
`Flapjack.PanValueFfiClockSemantics`: a successful run is unchanged -- same
outcome, same clock -- by any larger fuel.

Fuel and clock are different budgets and only the fuel is varied here. Fuel is
the recursion depth the evaluator is allowed; the clock is the resource the
program itself spends, and it is part of the result, so it must be preserved
exactly rather than relaxed.

Only the cases whose body mentions the fuel need an argument; the rest are one
wildcard alternative, so adding a `Prog` constructor does not renumber a list
of `case` names here. The clocked evaluator needs 12 alternatives against the
unclocked one's 25, because it routes most constructors through
`evalPanValueFfiClockLeaf`.

Added by pirapira/flapjack#659.
-/

namespace Flapjack

/-- Monotonicity statement for the clocked call evaluator (`motive1`). -/
def CallClockMono
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
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
      function arguments ma c mh = some result →
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock info
      function arguments ma c mh = some result

/-- Monotonicity statement for the clocked program evaluator (`motive2`). -/
def ProgClockMono
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
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) : Prop :=
  ∀ fuel' result, fuel ≤ fuel' →
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh = some result →
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock program
      ma c mh = some result

/-- The successor case of the clocked call evaluator, as a standalone lemma:
shared between `evalPanValueFfiClockProg_fuel_mono`'s `case2` and
`evalPanValueFfiClockCall_fuel_mono`, which differ only in where the two
program-evaluator induction hypotheses come from. -/
theorem call_clock_succ_mono
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
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (ihBody : ∀ (body : Prog α) (calleeLocals : VarName → Option (PanValue α)),
      ProgClockMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel calleeLocals globals memory ffi (clock - 1) body ma c mh)
    (ihHandler : ∀ (calleeClock : Nat) (calleeGlobals : VarName → Option (PanValue α))
      (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
      (value : PanValue α) (handlerVariable : VarName)
      (handlerProgram : Prog α),
      ProgClockMono context primitive handler structs functions baseAddress topAddress
        bytesInWord fuel (updatePanValueMap locals handlerVariable value) calleeGlobals
        calleeMemory calleeFfi calleeClock handlerProgram ma c mh) :
    CallClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord (fuel + 1) locals globals memory ffi clock info function arguments ma c mh := by
  intro fuel' result hle h
  obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
  have hfk : fuel ≤ k := by omega
  rw [evalPanValueFfiClockCall] at h
  rw [evalPanValueFfiClockCall]
  cases hargs : evalPanValueExps structs locals globals memory baseAddress
      topAddress bytesInWord arguments ma with
  | none => rw [hargs] at h; simp at h
  | some values =>
    rw [hargs] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    cases hlk : lookupPanFunction function functions with
    | none => rw [hlk] at h; simp at h
    | some pb =>
      obtain ⟨parameters, body⟩ := pb
      rw [hlk] at h
      simp only [Option.bind_some] at h ⊢
      by_cases hvalid : panValueParametersValid structs c function values
      · rw [if_pos hvalid] at h ⊢
        cases hbind : bindPanValueParameters parameters values with
        | none => rw [hbind] at h; simp at h
        | some calleeLocals =>
          rw [hbind] at h
          simp only [Option.bind_some] at h ⊢
          by_cases hclock : clock = 0
          · rw [if_pos hclock] at h ⊢; exact h
          · rw [if_neg hclock] at h ⊢
            cases hbody : evalPanValueFfiClockProg context primitive handler structs
                functions baseAddress topAddress bytesInWord fuel calleeLocals globals
                memory ffi (clock - 1) body ma c mh with
            | none => rw [hbody] at h; simp at h
            | some rp =>
              obtain ⟨outcome, calleeClock⟩ := rp
              rw [hbody] at h
              rw [ihBody body calleeLocals _ _ hfk hbody]
              simp only [Option.bind_some] at h ⊢
              cases outcome with
              | timeout l cg cm cf => exact h
              | control res =>
                cases res with
                | normal l cg cm cf => exact h
                | broke l cg cm cf => exact h
                | continued l cg cm cf => exact h
                | returned l cg cm cf vs => exact h
                | finalFfi l cg cm cf ev => exact h
                | raised l cg cm cf e v =>
                  dsimp only at h ⊢
                  by_cases hev :
                      (panValueExceptionValid structs c e v &&
                        panValuePayloadWithinLimit structs v) = true
                  · rw [if_pos hev] at h ⊢
                    cases info with
                    | none => exact h
                    | some pr =>
                      obtain ⟨destination, handlerInfo⟩ := pr
                      cases handlerInfo with
                      | none => exact h
                      | some triple =>
                        obtain ⟨caught, handlerVariable, handlerProgram⟩ := triple
                        dsimp only at h ⊢
                        by_cases hcaught : (caught == e) = true
                        · rw [if_pos hcaught] at h ⊢
                          by_cases hhv :
                              panValueHandlerValid structs c locals handlerVariable v
                          · rw [if_pos hhv] at h ⊢
                            exact ihHandler _ _ _ _ _ _ _ _ _ hfk h
                          · rw [if_neg hhv] at h; simp at h
                        · rw [if_neg hcaught] at h ⊢; exact h
                  · rw [if_neg hev] at h; simp at h
      · rw [if_neg hvalid] at h; simp at h

theorem evalPanValueFfiClockProg_fuel_mono'
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    ProgClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi clock program ma c mh := by
  intro fuel locals globals memory ffi clock program ma c mh
  induction fuel, locals, globals, memory, ffi, clock, program, ma, c, mh using
    evalPanValueFfiClockProg.induct (motive1 := CallClockMono context primitive handler
      structs functions baseAddress topAddress bytesInWord) with
  | case1 =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockCall] at h
    simp at h
  | case2 fuel locals globals memory ffi clock info function arguments ma c mh
      ihBody ihHandler =>
    exact call_clock_succ_mono context primitive handler structs functions baseAddress
      topAddress bytesInWord fuel locals globals memory ffi clock info function arguments
      ma c mh ihBody ihHandler
  | case3 =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockProg] at h
    simp at h
  | case4 fuel locals globals memory ffi clock name shape valueExp body ma c mh ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hv : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord valueExp ma with
    | none => rw [hv] at h; simp at h
    | some value =>
      rw [hv] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      by_cases hshape : panShapeMatches (panValueShape structs value) shape
      · rw [if_pos hshape] at h ⊢
        cases hb : evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name value)
            globals memory ffi clock body ma c mh with
        | none => rw [hb] at h; simp at h
        | some q =>
          rw [hb] at h
          rw [ihBody value _ _ hfk hb]
          exact h
      · rw [if_neg hshape] at h; simp at h
  | case5 fuel locals globals memory ffi clock first second ma c mh ihFirst ihSecond =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hf : evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first ma c mh with
    | none => rw [hf] at h; simp at h
    | some p =>
      obtain ⟨firstOutcome, firstClock⟩ := p
      rw [hf] at h
      rw [ihFirst _ _ hfk hf]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases firstOutcome with
      | control r =>
        cases r with
        | normal l g m f =>
          dsimp only at h ⊢
          cases hs : evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel l g m f firstClock second ma c mh with
          | none => rw [hs] at h; simp at h
          | some q =>
            rw [hs] at h
            rw [ihSecond _ _ _ _ _ _ _ hfk hs]
            exact h
        | returned l g m f vs => exact h
        | raised l g m f e v => exact h
        | broke l g m f => exact h
        | continued l g m f => exact h
        | finalFfi l g m f ev => exact h
      | timeout l g m f => exact h
  | case6 fuel locals globals memory ffi clock condition thenBranch elseBranch ma c mh
      ihBranch =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hc : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord condition ma with
    | none => rw [hc] at h; simp at h
    | some cv =>
      rw [hc] at h
      cases cv with
      | word w =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        exact ihBranch _ _ _ hfk h
      | rStruct fields => simp at h
      | nStruct name fields => simp at h
  | case7 fuel locals globals memory ffi clock info function arguments ma c mh ihCall =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact ihCall _ _ hfk h
  | case8 fuel locals globals memory ffi clock name shape function arguments body ma c mh
      ihCall ihBody =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hcall : evalPanValueFfiClockCall context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock none
        function arguments ma c mh with
    | none => rw [hcall] at h; simp at h
    | some p =>
      obtain ⟨callOutcome, callClock⟩ := p
      rw [hcall] at h
      rw [ihCall _ _ hfk hcall]
      simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases callOutcome with
      | control r =>
        cases r with
        | returned l g m f vs =>
          cases vs with
          | nil => simp at h
          | cons value rest =>
            cases rest with
            | cons _ _ => simp at h
            | nil =>
              dsimp only at h ⊢
              by_cases hshape : panShapeMatches (panValueShape structs value) shape
              · rw [if_pos hshape] at h ⊢
                cases hb : evalPanValueFfiClockProg context primitive handler structs
                  functions baseAddress topAddress bytesInWord fuel
                  (updatePanValueMap locals name value) g m f callClock body ma c mh with
                | none => rw [hb] at h; simp at h
                | some q =>
                  rw [hb] at h
                  rw [ihBody _ _ _ _ _ _ _ hfk hb]
                  exact h
              · rw [if_neg hshape] at h; simp at h
        | raised l g m f e v => exact h
        | normal l g m f => simp at h
        | broke l g m f => simp at h
        | continued l g m f => simp at h
        | finalFfi l g m f ev => simp at h
      | timeout l g m f => simp at h
  | case9 fuel locals globals memory ffi clock conditionExp body ma c mh ihBody ihLoop =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    have hfk : fuel ≤ k := by omega
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    cases hc : evalPanValueExp structs locals globals memory baseAddress topAddress
        bytesInWord conditionExp ma with
    | none => rw [hc] at h; simp at h
    | some condition =>
      rw [hc] at h
      cases condition with
      | word cv =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
        by_cases hz : (cv == 0) = true
        · rw [if_pos hz] at h ⊢; exact h
        · rw [if_neg hz] at h ⊢
          by_cases hclock : (clock == 0) = true
          · rw [if_pos hclock] at h ⊢; exact h
          · rw [if_neg hclock] at h ⊢
            cases hb : evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel locals globals memory ffi (clock - 1)
                body ma c mh with
            | none => rw [hb] at h; simp at h
            | some bodyPair =>
              obtain ⟨bodyOutcome, bodyClock⟩ := bodyPair
              rw [hb] at h
              rw [ihBody _ _ hfk hb]
              simp only [Option.bind_some] at h ⊢
              cases bodyOutcome with
              | control r =>
                cases r with
                | normal l g m f =>
                  dsimp only at h ⊢
                  cases hl : evalPanValueFfiClockProg context primitive handler structs
                    functions baseAddress topAddress bytesInWord fuel l g m f bodyClock
                      (Prog.while conditionExp body) ma c mh with
                  | none => rw [hl] at h; simp at h
                  | some loopPair =>
                    rw [hl] at h
                    rw [ihLoop _ _ _ _ _ _ _ hfk hl]
                    exact h
                | continued l g m f =>
                  dsimp only at h ⊢
                  cases hl : evalPanValueFfiClockProg context primitive handler structs
                    functions baseAddress topAddress bytesInWord fuel l g m f bodyClock
                      (Prog.while conditionExp body) ma c mh with
                  | none => rw [hl] at h; simp at h
                  | some loopPair =>
                    rw [hl] at h
                    rw [ihLoop _ _ _ _ _ _ _ hfk hl]
                    exact h
                | returned l g m f vs => exact h
                | raised l g m f e v => exact h
                | broke l g m f => exact h
                | finalFfi l g m f ev => exact h
              | timeout l g m f => exact h
      | rStruct fields => simp at h
      | nStruct nm fields => simp at h
  | case10 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact h
  | case11 =>
    intro fuel' result hle h
    obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [evalPanValueFfiClockProg] at h
    rw [evalPanValueFfiClockProg]
    exact h
  | case12 =>
    -- the leaf delegation: every remaining constructor goes through
    -- `evalPanValueFfiClockLeaf`, which does not mention the fuel at all.
    all_goals intro fuel' result hle h
    all_goals obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    all_goals rw [evalPanValueFfiClockProg] at h ⊢
    all_goals first
      | exact h
      | assumption

/-- Fuel monotonicity for the clocked call evaluator, from
`evalPanValueFfiClockProg_fuel_mono'`. -/
theorem evalPanValueFfiClockCall_fuel_mono'
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    : ∀ (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)),
    CallClockMono context primitive handler structs functions baseAddress topAddress
      bytesInWord fuel locals globals memory ffi clock info function arguments ma c mh := by
  intro fuel locals globals memory ffi clock info function arguments ma c mh
  cases fuel with
  | zero =>
    intro fuel' result hle h
    rw [evalPanValueFfiClockCall] at h
    simp at h
  | succ n =>
    exact call_clock_succ_mono context primitive handler structs functions baseAddress
      topAddress bytesInWord n locals globals memory ffi clock info function arguments ma c mh
      (fun body calleeLocals => evalPanValueFfiClockProg_fuel_mono' context primitive
        handler structs functions baseAddress topAddress bytesInWord n calleeLocals globals
        memory ffi (clock - 1) body ma c mh)
      (fun calleeClock cg cm cf value hv hp => evalPanValueFfiClockProg_fuel_mono' context
        primitive handler structs functions baseAddress topAddress bytesInWord n
        (updatePanValueMap locals hv value) cg cm cf calleeClock hp ma c mh)

/-! ## The ergonomic forms -/

/-- **Fuel monotonicity for the clocked program evaluator.** -/
theorem evalPanValueFfiClockProg_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuel fuel' : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α)
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hfuel : fuel ≤ fuel')
    (hrun : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program
      ma c mh = some result) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock program
      ma c mh = some result :=
  evalPanValueFfiClockProg_fuel_mono' context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi clock program ma c mh
    fuel' result hfuel hrun

/-- **Fuel monotonicity for the clocked call evaluator.** -/
theorem evalPanValueFfiClockCall_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    {fuel fuel' : Nat}
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (ma : Option (PanValueMemoryAccess α)) (c : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    {result : PanValueFfiClockResult α σ}
    (hfuel : fuel ≤ fuel')
    (hrun : evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
      function arguments ma c mh = some result) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel' locals globals memory ffi clock info
      function arguments ma c mh = some result :=
  evalPanValueFfiClockCall_fuel_mono' context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function
    arguments ma c mh fuel' result hfuel hrun

/-- **Fuel monotonicity for the public clocked evaluator.** As with the stepped
entry point, the clock is preserved exactly; only the fuel is relaxed. -/
theorem evalPanValueFfiClockProgram_fuel_mono
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    {fuel fuel' : Nat} (hfuel : fuel ≤ fuel') (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    {ma : Option (PanValueMemoryAccess α)}
    {mh : Option (PanValueMemoryFfiHandler α σ)}
    {result : PanValueFfiClockResult α σ}
    (hrun : evalPanValueFfiClockProgram context initial clock primitive handler fuel
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel'
      declarations entry arguments (memoryAccess := ma) (memoryHandler := mh) = some result := by
  unfold evalPanValueFfiClockProgram at hrun ⊢
  cases hstate : evalPanValueDeclarations initial.source declarations (memoryAccess := ma) with
  | none => rw [hstate] at hrun; simp at hrun
  | some state =>
    rw [hstate] at hrun
    simp only [Option.bind_eq_bind, Option.bind_some] at hrun ⊢
    cases hcall : evalPanValueFfiClockCall context primitive handler state.structs
        state.functions state.baseAddress state.topAddress state.bytesInWord fuel
        (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
        ma (some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes)) mh with
    | none => rw [hcall] at hrun; simp at hrun
    | some callResult =>
      rw [hcall] at hrun
      rw [evalPanValueFfiClockCall_fuel_mono' context primitive handler state.structs
        state.functions state.baseAddress state.topAddress state.bytesInWord fuel
        (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
        ma (some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes)) mh _ _ hfuel hcall]
      exact hrun


end Flapjack
