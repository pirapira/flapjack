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
    (ffi function configuration configurationLength array arrayLength
      (crepStateOfLoopState state)).map loopStateOfCrepState

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

def loopControlLocal (name : Nat) : LoopResult α → Option α
  | .normal state => state.locals name
  | .returned state _ => state.locals name
  | .raised state _ => state.locals name
  | .broke state _ => state.locals name
  | .continued state _ => state.locals name

theorem crepToLoop_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
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

theorem crepToLoop_raise_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
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
    [DecidableRel (fun left right : α => left < right)]
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
    [DecidableRel (fun left right : α => left < right)]
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
    [DecidableRel (fun left right : α => left < right)]
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
    loopReadLocals, loopBindParameters, loopAssignValues, updateLoopLocal,
    evalLoopCondition, loopResultValues, hcontext, hloop]

theorem crepToLoop_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)]
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

end Flapjack
