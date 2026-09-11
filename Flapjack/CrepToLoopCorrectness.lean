import Flapjack.CorrectnessFfi
import Flapjack.CrepeSemantics

/-!
Crepe-to-Loop correctness for the FFI boundary.

The two evaluators use different state records even though an `extCall` has
the same observable effect in both languages.  These adapters make that
correspondence explicit and keep the proof independent of the implementation
details of `loopCompileProg`.
-/

namespace Flapjack

def loopStateOfCrepState (state : CrepState α) : LoopState α :=
  { locals := state.locals
    globals := fun _ => none
    memory := state.memory }

def crepStateOfLoopState (state : LoopState α) : CrepState α :=
  { locals := state.locals
    memory := state.memory }

def loopFfiOfCrepFfi (ffi : CrepFfiHandler α) :
    FunName → α → α → α → α → LoopState α → Option (LoopState α) :=
  fun function configuration configurationLength array arrayLength state =>
    match ffi function configuration configurationLength array arrayLength
      (crepStateOfLoopState state) with
    | some (.returned state) => some (loopStateOfCrepState state)
    | some (.final _) | none => none

def crepControlValues : CrepControlResult α → List α
  | .returned _ values => values
  | _ => []

def crepControlException : CrepControlResult α → Option α
  | .raised _ exception => some exception
  | _ => none

def loopControlException : LoopResult α → Option α
  | .raised _ exception => some exception
  | _ => none

def crepControlLocal (name : Nat) : CrepControlResult α → Option α
  | .normal state => state.locals name
  | .returned state _ => state.locals name
  | .raised state _ => state.locals name
  | .broke state _ => state.locals name
  | .continued state _ => state.locals name
  | .finalFfi state _ => state.locals name

def loopControlLocal (name : Nat) : LoopResult α → Option α
  | .normal state => state.locals name
  | .returned state _ => state.locals name
  | .raised state _ => state.locals name
  | .broke state _ => state.locals name
  | .continued state _ => state.locals name

def crepControlMemoryAt (address : α) : CrepControlResult α → Option α
  | .normal state => state.memory address
  | .returned state _ => state.memory address
  | .raised state _ => state.memory address
  | .broke state _ => state.memory address
  | .continued state _ => state.memory address
  | .finalFfi state _ => state.memory address

def loopControlMemoryAt (address : α) : LoopResult α → Option α
  | .normal state => state.memory address
  | .returned state _ => state.memory address
  | .raised state _ => state.memory address
  | .broke state _ => state.memory address
  | .continued state _ => state.memory address

theorem crepToLoop_seq_normal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithCallsAndFfi loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState middle)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) = some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoop_seq_terminal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some result)
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) = some loopResult)
    (hcrepTerminal : ∀ middle : CrepState α, result ≠ .normal middle)
    (hloopTerminal : ∀ middle : LoopState α, loopResult ≠ .normal middle) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) = some loopResult := by
  constructor
  · simp only [evalCrepFullProg]
    rw [hfirst]
    cases result with
    | normal middle => exact (hcrepTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl
    | finalFfi state event => rfl
  · simp only [loopCompileProg_seq, evalLoopProgWithCallsAndFfi]
    rw [hloopFirst]
    cases loopResult with
    | normal middle => exact (hloopTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl

theorem crepToLoop_assign_agreement_of_empty_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (expression : CrepExp α) (value : α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress expression =
      some value)
    (heval : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name expression)).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name expression))).map
        (loopControlLocal name) := by
  have heval' : evalLoopExp
      ({ locals := state.locals
         globals := fun _ => none
         memory := state.memory } : LoopState α)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value := by
    simpa [loopStateOfCrepState] using heval
  simp [evalCrepFullProg, hvalue,
    loopCompileProg, hcode, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, heval',
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal]

theorem crepToLoop_assign_load32_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (address value : α)
    (hmemory : state.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.load32 (.const address)))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.assign name (.load32 (.const address))))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp, hmemory,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal]

theorem crepToLoop_assign_loadByte_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (address value : α)
    (hmemory : state.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.loadByte (.const address)))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.assign name (.loadByte (.const address))))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp, hmemory,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal]

theorem crepToLoop_store_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (address value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.store (.const address) (.const value))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 4)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.store (.const address) (.const value)))).map
        (loopControlMemoryAt address) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    crepControlMemoryAt, loopControlMemoryAt,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateMemory, updateLoopMemory,
    updateLoopLocal]

theorem crepToLoop_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.return [.const value])).map crepControlValues =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.return [.const value]))).map loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp, crepControlValues,
    loopCompileProg,
    loopCompileExp, loopCompileExp.loopCompileExps, loopCompileExps,
    loopNestedSeq, loopTempNames, loopAssignTemps,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, loopResultValues]

/-!
The assignment case is the first state-transforming Crep-to-Loop boundary.
`loopCompileProg` introduces the same constant assignment after an empty
expression-code prefix; the extra unit of fuel accounts for that generated
sequence node.  The theorem observes the assigned slot rather than equating
the two state representations wholesale, which is the relation consumed by
the later Loop-to-Word proof.
-/
theorem crepToLoop_assign_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.const value))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name (.const value)))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopCompileProg, loopCompileExp,
    loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopControlLocal]

theorem crepToLoop_assign_var_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name source : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.var source))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name (.var source)))).map
        (loopControlLocal name) := by
  cases hsource : state.locals source with
  | none =>
      simp [evalCrepFullProg, evalCrepFullExp,
        loopStateOfCrepState, loopCompileProg, loopCompileExp,
        loopNestedSeq,
        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        hsource]
  | some sourceValue =>
      apply crepToLoop_assign_agreement_of_empty_prefix
        context functions primitive ffi sharedMem baseAddress topAddress fuel
        state live name (.var source) sourceValue
      · simp [loopCompileExp]
      · simp [evalCrepFullExp, hsource]
      · simp [loopStateOfCrepState, loopCompileExp, evalLoopExp, hsource]

theorem crepToLoop_raise_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (exception : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.raise exception)).map crepControlException =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 8)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.raise exception))).map loopControlException := by
  simp [evalCrepFullProg, crepControlException, loopControlException,
    loopCompileProg, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, updateLoopLocal]

theorem crepToLoop_call_skip_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.skip : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], (.skip : LoopProg α))) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 4) state (.call none function []) =
      some (.normal state) ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 4)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function [])) =
      some (.normal (loopStateOfCrepState state)) := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
      assignCrepValues, hcrep]
  · have hskip (n : Nat) (loopState : LoopState α) :
        evalLoopProg (n + 1) loopState (.skip : LoopProg α) =
          some (.normal loopState) := by
      simp [evalLoopProg]
    simp [loopCompileProg, loopCompileExps,
      loopCompileExp.loopCompileExps, loopTempNames, loopAssignTemps,
      loopNestedSeq, evalLoopProgWithCallsAndFfi,
      evalLoopCallWithCallsAndFfi, loopReadLocals, loopBindParameters,
      hcontext, hloop, hskip]

theorem crepToLoop_call_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target parameter destination : Nat) (value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([parameter], (.return [.var parameter] : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 1))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([parameter], (.return [parameter] : LoopProg α))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 8) state
        (.call (some ([destination], none)) function [.const value])).map
        (crepControlLocal destination) =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 8)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([destination], none)) function [.const value]))).map
        (loopControlLocal destination) := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, updateCrepLocal,
    crepControlLocal, hcrep, loopCompileProg, loopCompileExps,
    loopCompileExp.loopCompileExps, loopCompileExp_const, loopTempNames,
    loopAssignTemps,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi,
    evalLoopProg, evalLoopExp, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopControlLocal, hcontext, hloop]

theorem crepToLoop_call_caught_skip_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state
        (.call (some ([], some (exception, .skip))) function [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .skip))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlValues, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq, evalLoopProgWithCallsAndFfi,
    evalLoopCallWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    evalLoopCondition, loopResultValues, hcontext, hloop]

theorem crepToLoop_call_uncaught_raise_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state (.call none function [])).map crepControlException =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function []))).map
        loopControlException := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlException, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq, evalLoopProgWithCallsAndFfi,
    evalLoopCallWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    loopControlException, hcontext, hloop]

theorem crepToLoop_call_caught_return_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 30) state
        (.call (some ([], some (exception, .return [.const value]))) function [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 30)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .return [.const value]))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, crepControlValues, hcrep,
    loopCompileProg, loopCompileExps, loopCompileExp.loopCompileExps,
    loopCompileExp_const, loopTempNames, loopAssignTemps, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi, evalLoopProg,
    evalLoopExp, evalLoopCondition, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopResultValues, hcontext, hloop]

/-! A caught call may run an arbitrary handler program, including one that
    performs an FFI step.  This boundary theorem leaves the two handler
    executions as explicit hypotheses and relates the observable returned
    values after the caller/callee local restoration performed by each
    evaluator. -/

theorem crepToLoop_call_caught_handler_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (loopCaller : LoopState α)
    (function : FunName) (target : Nat) (handlerVar : Nat)
    (caught exception : α) (crepBody : CrepProg α) (loopBody : LoopProg α)
    (crepHandler : CrepProg α) (loopHandler : LoopProg α)
    (crepCallee : CrepState α) (loopCallee : LoopState α)
    (crepResult : CrepControlResult α) (loopResult : LoopResult α)
    (hloopCaller : loopCaller = loopStateOfCrepState caller)
    (hcrepLookup : lookupCompiledFunction function crepFunctions =
      some ([], crepBody))
    (hloopLookup : lookupLoopFunction target loopFunctions =
      some ([], loopBody))
    (hcaught : caught == exception)
    (hcrepCallee : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := fun _ => none, memory := caller.memory } crepBody =
      some (.raised crepCallee exception))
    (hloopCallee : evalLoopProgWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := fun _ => none, globals := loopCaller.globals,
        memory := loopCaller.memory } loopBody =
      some (.raised loopCallee exception))
    (hhandler : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := caller.locals, memory := crepCallee.memory } crepHandler =
      some crepResult)
    (hloopHandler : evalLoopProgWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := updateLoopLocal loopCaller.locals handlerVar exception,
        globals := loopCallee.globals, memory := loopCallee.memory } loopHandler =
      some loopResult)
    (hvalues : crepControlValues crepResult = loopResultValues loopResult) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) caller
      (.call (some ([], some (caught, crepHandler))) function [])).map
        crepControlValues =
    (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
      (fuel + 2) loopCaller
      (.call (some ([], [])) (some target) []
        (some (handlerVar, loopHandler, .skip, [])))).map
        loopResultValues := by
  subst loopCaller
  have hcrepCall := evalCrepFullCall_caught_handler
    crepFunctions primitive ffi sharedMem baseAddress topAddress fuel caller
    function [] caught crepHandler [] [] [] crepBody
    (fun _ => none) crepCallee exception crepResult
    (by simp [evalCrepFullExps]) hcrepLookup rfl hcrepCallee hcaught hhandler
  have hloopCall : evalLoopCallWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) (fuel + 1) (loopStateOfCrepState caller)
      (some ([], [])) (some target) []
      (some (handlerVar, loopHandler, .skip, [])) =
      some loopResult := by
    simp [evalLoopCallWithCallsAndFfi, hloopLookup,
      loopReadLocals, loopBindParameters, hloopCallee, hloopHandler]
  simp [evalCrepFullProg, hcrepCall, evalLoopProgWithCallsAndFfi,
    hloopCall, hvalues]

theorem crepToLoop_seq_extCall_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (value : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
      (fuel + 20) state
      (.seq (.extCall function configuration configurationLength array arrayLength)
        (.return [.const value]))).map crepControlValues =
    (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.extCall function configuration configurationLength array arrayLength)
          (.return [.const value])))).map loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    crepControlValues, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopCompileProg, loopCompileExps,
    loopCompileExp.loopCompileExps, loopCompileExp_const, loopTempNames,
    loopAssignTemps, loopNestedSeq, loopReadLocals, updateLoopLocal,
    loopResultValues, loopFfiOfCrepFfi, crepStateOfLoopState,
    loopStateOfCrepState, hconfiguration, hconfigurationLength, harray,
    harrayLength, hffi]

theorem crepToLoop_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) =
      some (.normal state') ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (loopStateOfCrepState state')) := by
  constructor
  · exact evalCrepFullProg_extCall crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel state state' function configuration
      configurationLength array arrayLength configurationValue
      configurationLengthValue arrayValue arrayLengthValue hconfiguration
      hconfigurationLength harray harrayLength hffi
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

/-! An unavailable host service is observable as failure in both evaluators.
    Keeping this equation beside the successful FFI boundary prevents callers
    from accidentally treating the Loop adapter's `none` as a normal state
    transition. -/
theorem crepToLoop_extCall_failure_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = none) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) = none := by
  constructor
  · simp [evalCrepFullProg, hconfiguration, hconfigurationLength, harray,
      harrayLength, hffi]
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

/-! The pure Crepe-to-Loop adapter deliberately projects terminal FFI events
    away: `evalCrepFullResult` and the legacy Loop evaluator both expose only
    ordinary result values.  The stateful `LoopFfi` boundary retains the event
    separately; this theorem records the compatibility projection explicitly. -/
theorem crepToLoop_extCall_final_projection_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : FfiFinalEvent)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some (.final event)) :
    evalCrepFullResult crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) = none := by
  constructor
  · simp [evalCrepFullResult, evalCrepFullProg, hconfiguration,
      hconfigurationLength, harray, harrayLength, hffi]
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

theorem crepToLoop_seq_extCall_final_projection_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : FfiFinalEvent) (second : CrepProg α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some (.final event)) :
    evalCrepFullResult crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 2)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = none := by
  constructor
  · simp [evalCrepFullResult, evalCrepFullProg, hconfiguration,
      hconfigurationLength, harray, harrayLength, hffi]
  · have hfirst := crepToLoop_extCall_final_projection_agreement
      context crepFunctions loopFunctions primitive ffi sharedMem
      baseAddress topAddress fuel state live function configuration
      configurationLength array arrayLength configurationValue
      configurationLengthValue arrayValue arrayLengthValue event
      hconfiguration hconfigurationLength harray harrayLength hffi
    simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2]

/-! Failure also short-circuits a continuation.  This is the negative
    sequencing counterpart to `crepToLoop_seq_extCall_agreement`. -/
theorem crepToLoop_seq_extCall_failure_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (second : CrepProg α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = none) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 2) (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = none := by
  have hfirst := crepToLoop_extCall_failure_agreement context crepFunctions
    loopFunctions primitive ffi sharedMem baseAddress topAddress fuel state live
    function configuration configurationLength array arrayLength
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    hconfiguration hconfigurationLength harray harrayLength hffi
  constructor
  · simp [evalCrepFullProg, hfirst.1]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2]

/-! Once the first FFI action has been related, sequence evaluation is just
    state-threaded composition.  The continuation hypothesis is deliberately
    arbitrary: this is the reusable boundary needed to grow the complete
    source-to-Loop simulation without reproving the evaluator plumbing for
    every second statement. -/
theorem crepToLoop_seq_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state')
    (hsecond :
      evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state' second = some result)
    (hloopSecond :
      evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 1) (loopStateOfCrepState state')
        (loopCompileProg context live second) =
        some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 2) (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = some loopResult := by
  have hfirst := crepToLoop_extCall_agreement context crepFunctions loopFunctions
    primitive ffi sharedMem baseAddress topAddress fuel state state' live function
    configuration configurationLength array arrayLength configurationValue
    configurationLengthValue arrayValue arrayLengthValue hconfiguration
    hconfigurationLength harray harrayLength hffi
  constructor
  · simp [evalCrepFullProg, hfirst.1, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2, hloopSecond]

end Flapjack
