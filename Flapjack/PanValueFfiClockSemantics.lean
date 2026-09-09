import Flapjack.PanValueFfiSemantics

/-!
# Clocked structured Pancake semantics

This module adds the clock/timeout part of CakeML's `panSem` boundary to the
canonical structured, stateful-FFI evaluator.  The existing evaluator remains
available for compatibility and for proofs that do not model a clock.  The
clocked evaluator charges one unit at a function call, at each executed while
iteration, and at `Tick`, exactly as `dec_clock` is used by `panSem`.

Errors continue to be represented by `none`, while timeout is explicit and
clears source locals.  Keeping timeout in a separate result type avoids
changing the established control-result API used by the compiler proofs.
-/

namespace Flapjack

inductive PanValueFfiClockOutcome (α : Type u) (σ : Type v) where
  | control (result : PanValueFfiControlResult α σ)
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)

abbrev PanValueFfiClockResult (α : Type u) (σ : Type v) :=
  PanValueFfiClockOutcome α σ × Nat

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
    (contracts : Option PanValueCallContracts := none) :
    Option (PanValueFfiClockResult α σ) :=
  (evalPanValueFfiProgSteps context primitive handler structs functions
    baseAddress topAddress bytesInWord 1 locals globals memory ffi program
    (memoryAccess := memoryAccess) (contracts := contracts)).map
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
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, info, function, arguments,
        memoryAccess, contracts => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        let calleeLocals ← bindPanValueParameters parameters values
        if clock = 0 then
          pure (panValueFfiClockTimeout globals memory ffi clock)
        else
          let (outcome, calleeClock) ← evalPanValueFfiClockProg context primitive handler
            structs functions baseAddress topAddress bytesInWord fuel calleeLocals
            globals memory ffi (clock - 1) body
            (memoryAccess := memoryAccess) (contracts := contracts)
          match outcome with
          | .timeout _ calleeGlobals calleeMemory calleeFfi =>
              pure (.timeout (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                calleeClock)
          | .control result =>
              match result with
              | .normal _ _ _ _ | .broke _ _ _ _ | .continued _ _ _ _ => none
              | .returned _ calleeGlobals calleeMemory calleeFfi values =>
                  if panValueReturnValid structs contracts function values &&
                      panValueValuesWithinLimit structs values then
                    match info with
                    | none => pure (.control
                        (.returned (fun _ => none) calleeGlobals calleeMemory
                          calleeFfi values), calleeClock)
                    | some (destination, _) => do
                        let (callerLocals, callerGlobals) ←
                          assignPanValueCallResult locals calleeGlobals destination values
                            (structs := structs)
                        pure (.control (.normal callerLocals callerGlobals
                          calleeMemory calleeFfi), calleeClock)
                  else none
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
                          else none
                        else pure (.control (.raised (fun _ => none) calleeGlobals
                          calleeMemory calleeFfi exception value), calleeClock)
                    | _ => pure (.control (.raised (fun _ => none) calleeGlobals
                        calleeMemory calleeFfi exception value), calleeClock)
                  else none
              | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                  pure (.control (.finalFfi (fun _ => none) calleeGlobals
                    calleeMemory calleeFfi event), calleeClock)
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
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .dec name shape value body,
        memoryAccess, contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let (outcome, nextClock) ← evalPanValueFfiClockProg context primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory ffi clock body
            (memoryAccess := memoryAccess) (contracts := contracts)
          pure (panValueFfiClockRestoreLocal name oldValue outcome, nextClock)
        else none
    | fuel + 1, locals, globals, memory, ffi, clock, .seq first second,
        memoryAccess, contracts => do
        let (firstOutcome, firstClock) ← evalPanValueFfiClockProg context primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
          clock first (memoryAccess := memoryAccess) (contracts := contracts)
        match firstOutcome with
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
            evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
              firstClock second (memoryAccess := memoryAccess) (contracts := contracts)
        | _ => pure (firstOutcome, firstClock)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .ite condition thenBranch elseBranch, memoryAccess, contracts => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        evalPanValueFfiClockProg context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
          (if condition != 0 then thenBranch else elseBranch)
          (memoryAccess := memoryAccess) (contracts := contracts)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .call info function arguments, memoryAccess, contracts =>
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function
          arguments (memoryAccess := memoryAccess) (contracts := contracts)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .decCall name shape function arguments body, memoryAccess, contracts => do
        let oldValue := locals name
        let (outcome, nextClock) ← evalPanValueFfiClockCall context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
          none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
        match outcome with
        | .control (.returned _ nextGlobals nextMemory nextFfi [value]) =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi nextClock body
                (memoryAccess := memoryAccess) (contracts := contracts)
              pure (panValueFfiClockRestoreLocal name oldValue bodyOutcome, bodyClock)
            else none
        | .control (.raised _ nextGlobals nextMemory nextFfi exception value) =>
            pure (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
              exception value), nextClock)
        | _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .while conditionExp body,
        memoryAccess, contracts => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.control (.normal locals globals memory ffi), clock)
        else if clock == 0 then
          pure (panValueFfiClockTimeout globals memory ffi clock)
        else
          let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
            structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
            (clock - 1) body (memoryAccess := memoryAccess) (contracts := contracts)
          match bodyOutcome with
          | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
              .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
              evalPanValueFfiClockProg context primitive handler structs functions
                baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
                bodyClock (.while conditionExp body)
                (memoryAccess := memoryAccess) (contracts := contracts)
          | .control (.broke nextLocals nextGlobals nextMemory nextFfi) =>
              pure (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock)
          | _ => pure (bodyOutcome, bodyClock)
    | _fuel + 1, locals, globals, memory, ffi, clock, .tick, _, _ =>
        if clock = 0 then
          pure (panValueFfiClockTimeout globals memory ffi clock)
        else
          pure (.control (.normal locals globals memory ffi), clock - 1)
    | _fuel + 1, locals, globals, memory, ffi, clock, program, memoryAccess, contracts =>
        evalPanValueFfiClockLeaf context primitive handler structs functions
          baseAddress topAddress bytesInWord clock locals globals memory ffi program
          (memoryAccess := memoryAccess) (contracts := contracts)
    termination_by fuel _ _ _ _ _ _ _ => fuel
end

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
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValueFfiClockResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions)
  let (outcome, nextClock) ← evalPanValueFfiClockCall context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
  match lookupInfo entry state.returnShapes, outcome with
  | some shape, .control (.returned locals globals memory ffi [value]) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.control (.returned locals globals memory ffi [value]), nextClock)
      else none
  | some _, .control (.returned _ _ _ _ _) => none
  | _, outcome => some (outcome, nextClock)

end Flapjack
