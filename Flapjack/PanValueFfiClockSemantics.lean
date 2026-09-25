import Flapjack.PanValueFfiSemantics
import Flapjack.PanBst

/-!
# Clocked structured Pancake semantics

This module adds the clock/timeout part of CakeML's `panSem` boundary to the
canonical structured, stateful-FFI evaluator.  The existing evaluator remains
available for compatibility and for proofs that do not model a clock.  The
clocked evaluator charges one unit at a function call, at each executed while
iteration, and at `Tick`, exactly as `dec_clock` is used by `panSem`.

Semantic errors (`panSem`'s `SOME Error`) are explicit
`PanValueFfiControlResult.error` results carrying the unchanged state, while
timeout is explicit and clears source locals.  Only a genuinely missing
evaluation result (for example fuel exhaustion) is `none`.  Keeping timeout in
a separate result type avoids changing the established control-result API used
by the compiler proofs.
-/

namespace Flapjack

/-! Exact clock projection of Pancake's `dec_clock_def`
    (`cakeml/pancake/semantics/panSemScript.sml:441-443`).  The structured
    clock evaluator carries the state components separately, so this helper
    is the state-update equation's clock component. -/
abbrev decPanClock (clock : Nat) : Nat :=
  clock - 1

inductive PanValueFfiClockOutcome (α : Type u) (σ : Type v) where
  | control (result : PanValueFfiControlResult α σ)
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)

abbrev PanValueFfiClockResult (α : Type u) (σ : Type v) :=
  PanValueFfiClockOutcome α σ × Nat

/-! Exact clock projection of Pancake's `fix_clock_def`
    (`cakeml/pancake/semantics/panSemScript.sml:446-448`).  The result is
    unchanged and the returned clock is clamped to the smaller old/new
    clock.  This is transparent so existing clock proofs can still rewrite
    the underlying subtraction and minimum directly. -/
abbrev fixPanClock {β : Type u} (oldClock : Nat) (step : β × Nat) :
    β × Nat :=
  let (outcome, newClock) := step
  (outcome, min oldClock newClock)

def panValueFfiClockTimeout
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) : PanValueFfiClockResult α σ :=
  (.timeout (fun _ => none) globals memory ffi, clock)

def panValueFfiClockRestoreLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueFfiClockOutcome α σ → PanValueFfiClockOutcome α σ
  | .control result => .control (restorePanValueFfiLocal name oldValue result)
  | .timeout locals globals memory ffi =>
      .timeout (restorePanValueLocal locals name oldValue) globals memory ffi

def panValueFfiClockClearTimeoutLocals :
    PanValueFfiClockOutcome α σ → PanValueFfiClockOutcome α σ
  | .control result => .control result
  | .timeout _ globals memory ffi => .timeout (fun _ => none) globals memory ffi

def evalPanValueFfiClockLeaf
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
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  (evalPanValueFfiProgSteps context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 locals globals memory ffi program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)).map
    (fun (result, _) => (.control result, clock))

mutual
  def evalPanValueFfiClockCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (preserveReturnLocals : Bool := false) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, info, function, arguments,
        memoryAccess, contracts, memoryHandler, preserveReturnLocals => do
        (panValueCallArgumentsValue structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun values =>
            (panValueCallTarget structs contracts function functions values).elim
              (pure (.control (.error locals globals memory ffi), clock))
              (fun callTarget => do
              let (body, calleeLocals) := callTarget
              if clock = 0 then
                pure (panValueFfiClockTimeout globals memory ffi clock)
              else
                let (outcome, calleeClock) ← evalPanValueFfiClockProg context primitive handler
                  structs functions baseAddress topAddress bytesInWord fuel calleeLocals
                  globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
                match outcome with
                | .timeout _ calleeGlobals calleeMemory calleeFfi =>
                    pure (.timeout (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                      calleeClock)
                | .control result =>
                    match result with
                    | .normal calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .broke calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .continued calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .error _ calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error (fun _ => none) calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .returned _ calleeGlobals calleeMemory calleeFfi values =>
                        -- This functions-list compatibility carrier stores only
                        -- parameter names and the body; unlike HOL `state.code`,
                        -- it has no source `returnShape`.  Do not substitute the
                        -- optional, independently supplied `contracts` table for
                        -- that missing code-map field: doing so can reject a
                        -- return that HOL accepts.  The state-owned code-map
                        -- evaluator below performs the actual HOL shape check.
                        match info with
                        | none =>
                            let returnedLocals :=
                              if preserveReturnLocals then calleeLocals else fun _ => none
                            pure (.control
                            (.returned returnedLocals calleeGlobals calleeMemory
                              calleeFfi values), calleeClock)
                        | some (destination, _) => do
                            let (callerLocals, callerGlobals) ←
                              assignPanValueCallResult locals calleeGlobals destination values
                                (structs := structs)
                            pure (.control (.normal callerLocals callerGlobals
                              calleeMemory calleeFfi), calleeClock)
                    | .raised _ calleeGlobals calleeMemory calleeFfi exception value =>
                        if panValueExceptionValid structs contracts exception value &&
                            panValuePayloadWithinLimit structs value then
                          match info with
                          | some (_, some (caught, handlerVariable, handlerProgram)) =>
                              if caught == exception then
                                if panValueHandlerValid structs contracts locals handlerVariable value then
                                  evalPanValueFfiClockProg context primitive handler structs functions
                                    baseAddress topAddress bytesInWord fuel
                                    (updatePanValueMap locals handlerVariable value) calleeGlobals
                                    calleeMemory calleeFfi calleeClock handlerProgram
                                    (memoryAccess := memoryAccess) (contracts := contracts)
                                    (memoryHandler := memoryHandler)
                                else none
                              else pure (.control (.raised (fun _ => none) calleeGlobals
                                calleeMemory calleeFfi exception value), calleeClock)
                          | _ => pure (.control (.raised (fun _ => none) calleeGlobals
                              calleeMemory calleeFfi exception value), calleeClock)
                        else none
                    | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                        pure (.control (.finalFfi (fun _ => none) calleeGlobals
                          calleeMemory calleeFfi event), calleeClock)
              ))
    termination_by fuel _ _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiClockProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .dec name shape value body,
        memoryAccess, contracts, memoryHandler =>
        (panValueDecAcceptedValue structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun evaluated => do
            let oldValue := locals name
            let (outcome, nextClock) ← evalPanValueFfiClockProg context primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              (updatePanValueMap locals name evaluated) globals memory ffi clock body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (panValueFfiClockRestoreLocal name oldValue outcome, nextClock))
    | fuel + 1, locals, globals, memory, ffi, clock, .seq first second,
        memoryAccess, contracts, memoryHandler => do
        let (firstOutcome, firstClock) ← evalPanValueFfiClockProg context primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
          clock first (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match firstOutcome with
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
            evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
              firstClock second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
        | _ => pure (firstOutcome, firstClock)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory condition memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun condition =>
            evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
              (if condition != 0 then thenBranch else elseBranch)
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler))
    | fuel + 1, locals, globals, memory, ffi, clock,
        .call info function arguments, memoryAccess, contracts, memoryHandler =>
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function
          arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (outcome, nextClock) ← evalPanValueFfiClockCall context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
          none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (preserveReturnLocals := true)
        match outcome with
        | .control (.returned nextLocals nextGlobals nextMemory nextFfi [value]) =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi nextClock body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (panValueFfiClockRestoreLocal name oldValue bodyOutcome, bodyClock)
            -- HOL's mismatch branch returns the callee post-state `st`.
            else pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.raised _ nextGlobals nextMemory nextFfi exception value) =>
            pure (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
              exception value), nextClock)
        | .timeout nextLocals nextGlobals nextMemory nextFfi =>
            pure (.timeout nextLocals nextGlobals nextMemory nextFfi, nextClock)
        | .control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event) =>
            pure (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
              nextClock)
        | .control (.returned _ _ _ _ _) => none
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
            .control (.broke nextLocals nextGlobals nextMemory nextFfi) |
            .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
            -- HOL `DecCall` turns callee NONE/Break/Continue into Error and
            -- returns the fixed callee post-state unchanged.
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.error nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
    | fuel + 1, locals, globals, memory, ffi, clock, .while conditionExp body,
        memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun conditionValue =>
            if conditionValue == 0 then
              pure (.control (.normal locals globals memory ffi), clock)
            else if clock == 0 then
              pure (panValueFfiClockTimeout globals memory ffi clock)
            else do
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
                (decPanClock clock) body (memoryAccess := memoryAccess)
                (contracts := contracts)
                (memoryHandler := memoryHandler)
              match bodyOutcome with
              | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
                  .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
                  evalPanValueFfiClockProg context primitive handler structs functions
                    baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
                    bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler)
              | .control (.broke nextLocals nextGlobals nextMemory nextFfi) =>
                  pure (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock)
              | _ => pure (bodyOutcome, bodyClock))
    | _fuel + 1, locals, globals, memory, ffi, clock, .tick, _, _, _ =>
        if clock = 0 then
          pure (panValueFfiClockTimeout globals memory ffi clock)
        else
          pure (.control (.normal locals globals memory ffi), decPanClock clock)
    | _fuel + 1, locals, globals, memory, ffi, clock, program, memoryAccess, contracts,
        memoryHandler =>
        evalPanValueFfiClockLeaf context primitive handler structs functions
          baseAddress topAddress bytesInWord clock locals globals memory ffi program
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    termination_by fuel _ _ _ _ _ _ _ => fuel
end

/-! Source-state clock evaluator. Unlike the compatibility evaluator above,
    every Call and DecCall resolves directly from the finite code map that is
    threaded unchanged through recursive evaluation. This is an executable
    evaluator analogue exercised against direct HOL oracle cases; it is not
    tagged as a HOL theorem port because the full state-rel correspondence
    proof remains open. -/
mutual
  def evalPanValueFfiClockCodeCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (preserveReturnLocals : Bool := false) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, info, function, arguments,
        memoryAccess, contracts, memoryHandler, preserveReturnLocals => do
        (panValueCallArgumentsValue structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun values =>
            (lookupPanSemCodeCall structs code function values).elim
              (pure (.control (.error locals globals memory ffi), clock))
              (fun codeTarget => do
              let (body, returnShape, calleeLocals) := codeTarget
              if clock = 0 then
                pure (panValueFfiClockTimeout globals memory ffi clock)
              else
                let (outcome, calleeClock) ← evalPanValueFfiClockCodeProg context primitive handler
                  structs code exceptionShapes baseAddress topAddress bytesInWord fuel calleeLocals
                  globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
                let (outcome, calleeClock) :=
                  fixPanClock (decPanClock clock) (outcome, calleeClock)
                match outcome with
                | .timeout _ calleeGlobals calleeMemory calleeFfi =>
                    pure (.timeout (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                      calleeClock)
                | .control result =>
                    match result with
                    | .normal calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .broke calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .continued calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .error _ calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error (fun _ => none) calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .returned calleeLocals calleeGlobals calleeMemory calleeFfi values =>
                        let sourceReturnValid := match values with
                          | [value] => panShapeMatches (panValueShape structs value) returnShape
                          | _ => false
                        if sourceReturnValid then
                          -- The source code entry supplies `returnShape`; HOL
                          -- Call checks that shape directly. `contracts` is a
                          -- compatibility input and is not part of the HOL
                          -- state, so it must not impose a second return-shape
                          -- check here. The payload-size limit is enforced by
                          -- the callee's `Return` equation.
                          match info with
                          | none =>
                              let returnedLocals :=
                                if preserveReturnLocals then calleeLocals else fun _ => none
                              pure (.control
                              (.returned returnedLocals calleeGlobals calleeMemory
                                calleeFfi values), calleeClock)
                          | some (destination, _) =>
                              match assignPanValueCallResult locals calleeGlobals destination values
                                  (structs := structs) with
                              | some (callerLocals, callerGlobals) =>
                                  pure (.control (.normal callerLocals callerGlobals
                                    calleeMemory calleeFfi), calleeClock)
                              | none =>
                                  pure (.control (.error calleeLocals calleeGlobals
                                    calleeMemory calleeFfi), calleeClock)
                        else pure (.control (.error
                          (if preserveReturnLocals then calleeLocals else fun _ => none)
                          calleeGlobals calleeMemory calleeFfi), calleeClock)
                    | .raised calleeLocals calleeGlobals calleeMemory calleeFfi exception value =>
                        match info with
                        | some (_, some (caught, handlerVariable, handlerProgram)) =>
                            if caught == exception then
                              match exceptionShapes exception with
                              | some shape =>
                                  if panShapeMatches (panValueShape structs value) shape &&
                                      panValueAssignmentValid structs locals (fun _ => none)
                                        .local handlerVariable value then
                                    evalPanValueFfiClockCodeProg context primitive handler structs code
                                      exceptionShapes
                                      baseAddress topAddress bytesInWord fuel
                                      (updatePanValueMap locals handlerVariable value) calleeGlobals
                                      calleeMemory calleeFfi calleeClock handlerProgram
                                      (memoryAccess := memoryAccess) (contracts := contracts)
                                      (memoryHandler := memoryHandler)
                                  else
                                    pure (.control (.error calleeLocals calleeGlobals
                                      calleeMemory calleeFfi), calleeClock)
                              | none =>
                                  pure (.control (.error calleeLocals calleeGlobals
                                    calleeMemory calleeFfi), calleeClock)
                            else pure (.control (.raised (fun _ => none) calleeGlobals
                              calleeMemory calleeFfi exception value), calleeClock)
                        | _ => pure (.control (.raised (fun _ => none) calleeGlobals
                            calleeMemory calleeFfi exception value), calleeClock)
                    | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                        pure (.control (.finalFfi (fun _ => none) calleeGlobals
                          calleeMemory calleeFfi event), calleeClock)
              ))
    termination_by fuel _ _ _ _ _ _ _ _ _ _ => fuel

  /-- State-code `DecCall` helper. The helper consumes the returned value only
      after the state-owned callee has completed, runs the continuation at the
      caller's local environment, and restores the old destination binding. -/
  def evalPanValueFfiClockCodeDecCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        VarName → Shape → FunName → List (Exp α) → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, name, shape, function,
        arguments, body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (outcome, nextClock) ← evalPanValueFfiClockCodeCall context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals
          memory ffi clock none function arguments (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)
          (preserveReturnLocals := true)
        match outcome with
        | .control (.returned nextLocals nextGlobals nextMemory nextFfi [value]) =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockCodeProg
                context primitive handler structs code exceptionShapes baseAddress topAddress
                bytesInWord fuel (updatePanValueMap locals name value) nextGlobals nextMemory
                nextFfi nextClock body (memoryAccess := memoryAccess)
                (contracts := contracts) (memoryHandler := memoryHandler)
              pure (panValueFfiClockRestoreLocal name oldValue bodyOutcome, bodyClock)
            else
              pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.raised _ nextGlobals nextMemory nextFfi exception value) =>
            pure (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
              exception value), nextClock)
        | .timeout nextLocals nextGlobals nextMemory nextFfi =>
            pure (.timeout nextLocals nextGlobals nextMemory nextFfi, nextClock)
        | .control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event) =>
            pure (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event), nextClock)
        | .control (.returned _ _ _ _ _) => none
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
            .control (.broke nextLocals nextGlobals nextMemory nextFfi) |
            .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.error nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
    termination_by fuel _ _ _ _ _ _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiClockCodeProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .dec name shape value body,
        memoryAccess, contracts, memoryHandler =>
        (panValueDecAcceptedValue structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun evaluated => do
            let oldValue := locals name
            let (outcome, nextClock) ← evalPanValueFfiClockCodeProg context primitive handler
              structs code exceptionShapes baseAddress topAddress bytesInWord fuel
              (updatePanValueMap locals name evaluated) globals memory ffi clock body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (panValueFfiClockRestoreLocal name oldValue outcome, nextClock))
    | fuel + 1, locals, globals, memory, ffi, clock, .seq first second,
        memoryAccess, contracts, memoryHandler => do
        let (firstOutcome, firstClock) ← evalPanValueFfiClockCodeProg context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi
          clock first (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        let (firstOutcome, firstClock) := fixPanClock clock (firstOutcome, firstClock)
        match firstOutcome with
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
            evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
              baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
              firstClock second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
        | _ => pure (firstOutcome, firstClock)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory condition memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun condition =>
            evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
              baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
              (if condition != 0 then thenBranch else elseBranch)
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler))
    | fuel + 1, locals, globals, memory, ffi, clock,
        .call info function arguments, memoryAccess, contracts, memoryHandler =>
        evalPanValueFfiClockCodeCall context primitive handler structs code exceptionShapes
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
          function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptionShapes
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock name shape
          function arguments body (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    | _fuel + 1, locals, globals, memory, ffi, clock,
        .raise exception expression, memoryAccess, _contracts, _memoryHandler =>
        match evalPanValueExpCounted structs locals globals memory baseAddress topAddress
            bytesInWord expression (memoryAccess := memoryAccess) with
        | none => pure (.control (.error locals globals memory ffi), clock)
        | some (value, _) =>
            match exceptionShapes exception with
            | some shape =>
                if panShapeMatches (panValueShape structs value) shape &&
                    panValuePayloadWithinLimit structs value then
                  pure (.control (.raised (fun _ => none) globals memory ffi
                    exception value), clock)
                else pure (.control (.error locals globals memory ffi), clock)
            | none => pure (.control (.error locals globals memory ffi), clock)
    | fuel + 1, locals, globals, memory, ffi, clock, .while conditionExp body,
        memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun conditionValue =>
            if conditionValue == 0 then
              pure (.control (.normal locals globals memory ffi), clock)
            else if clock == 0 then
              pure (panValueFfiClockTimeout globals memory ffi clock)
            else do
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockCodeProg context primitive handler
                structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi
                (decPanClock clock) body (memoryAccess := memoryAccess)
                (contracts := contracts) (memoryHandler := memoryHandler)
              let (bodyOutcome, bodyClock) :=
                fixPanClock (decPanClock clock) (bodyOutcome, bodyClock)
              match bodyOutcome with
              | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
                  .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
                  evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
                    baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
                    bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler)
              | .control (.broke nextLocals nextGlobals nextMemory nextFfi) =>
                  pure (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock)
              | _ => pure (bodyOutcome, bodyClock))
    | _fuel + 1, locals, globals, memory, ffi, clock, .tick, _, _, _ =>
        if clock == 0 then pure (panValueFfiClockTimeout globals memory ffi clock)
        else pure (.control (.normal locals globals memory ffi), decPanClock clock)
    | _fuel + 1, locals, globals, memory, ffi, clock, program, memoryAccess, contracts,
        memoryHandler =>
        evalPanValueFfiClockLeaf context primitive handler structs []
          baseAddress topAddress bytesInWord clock locals globals memory ffi program
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    termination_by fuel _ _ _ _ _ _ _ _ _ => fuel
end

/-! General source Call exception-dispatch step.  The callee body, argument
values, return shape, exception payload, and handler program are all
parameters; `hcalleeBody` is the source-side induction hypothesis for the
callee.  This exposes the exact clock clamp and handler-local update used by
HOL `evaluate_def` without assuming a fixed callee syntax or a target run. -/
theorem evalPanValueFfiClockCodeCall_catchesRaisedBody
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (handlerVariable : VarName) (handlerProgram body : Prog α)
    (function : FunName) (exception : ExceptionId)
    (arguments : List (Exp α)) (values : List (PanValue α))
    (returnShape : Shape)
    (calleeLocals : VarName → Option (PanValue α))
    (calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (exceptionValue : PanValue α) (calleeClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (handlerResult : PanValueFfiClockResult α σ)
    (harguments : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hcallee : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, calleeLocals))
    (hclock : clock ≠ 0)
    (calleeRaisedLocals : VarName → Option (PanValue α))
    (hcalleeBody : evalPanValueFfiClockCodeProg context primitive handler
      structs code exceptionShapes baseAddress topAddress bytesInWord fuel
      calleeLocals globals memory ffi (decPanClock clock) body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
        some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory
          calleeFfi exception exceptionValue), calleeClock))
    (hexceptionShape : ∃ shape, exceptionShapes exception = some shape ∧
      panShapeMatches (panValueShape structs exceptionValue) shape = true)
    (hhandlerAssignment : panValueAssignmentValid structs locals (fun _ => none)
      .local handlerVariable exceptionValue = true)
    (hhandlerBody : evalPanValueFfiClockCodeProg context primitive handler
      structs code exceptionShapes baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable exceptionValue)
      calleeGlobals calleeMemory calleeFfi
      (min (decPanClock clock) calleeClock) handlerProgram
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some handlerResult) :
    evalPanValueFfiClockCodeCall context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals
      globals memory ffi clock
      (some (none, some (exception, handlerVariable, handlerProgram)))
      function arguments (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
        some handlerResult := by
  rcases hexceptionShape with ⟨shape, hshape, hshapeMatch⟩
  simp [evalPanValueFfiClockCodeCall, Option.elim_some, panValueCallArgumentsValue, harguments, hcallee, hclock,
    hcalleeBody, hshape, hshapeMatch, hhandlerAssignment, hhandlerBody, decPanClock]

def evalPanValueFfiClockProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let (outcome, nextClock) ← evalPanValueFfiClockCall context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, outcome with
  | some shape, .control (.returned locals globals memory ffi [value]) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.control (.returned locals globals memory ffi [value]), nextClock)
      else none
  | some _, .control (.returned _ _ _ _ _) => none
  | _, outcome => some (outcome, nextClock)

/-! A callee that falls through (`panSem`'s `NONE`) is a call failure: Cake's
    `evaluate (Call ...)` maps `(NONE,st) => (SOME Error,st)`, preserving the
    callee's post-call locals, globals, memory, FFI state and clock.  This is
    the direct-call `NONE` rejection branch. -/
theorem evalPanValueFfiClockCall_callee_normal_error
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A callee that finishes with `break` is a call failure: Cake's
    `evaluate (Call ...)` maps `(SOME Break,st) => (SOME Error,st)`, preserving
    the callee's post-call locals, globals, memory, FFI state and clock. -/
theorem evalPanValueFfiClockCall_callee_broke_error
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.broke bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A callee that finishes with `continue` is a call failure: Cake's
    `evaluate (Call ...)` maps `(SOME Continue,st) => (SOME Error,st)`, preserving
    the callee's post-call locals, globals, memory, FFI state and clock. -/
theorem evalPanValueFfiClockCall_callee_continued_error
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.continued bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-- Flapjack's clocked Call equation for a callee Error: the catch-all Call
    branch preserves the callee's final nonlocal state and clears its locals.
    Untagged because this evaluator uses a structured control result rather
    than HOL's `result option × state` pair. -/
theorem evalPanValueFfiClockCall_callee_error_error
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
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error (fun _ => none) finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]


end Flapjack
