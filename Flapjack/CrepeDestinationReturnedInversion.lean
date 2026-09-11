import Flapjack.CrepeCallNormalInversion
import Flapjack.CrepeReturnedBranchSelection

/-!
Destination-aware normal-call inversion specialized to a recursively correct
returned callee.  The generic inversion admits a normal callee branch; the
branch-selection lemma removes it and exposes the returned-value assignment
needed by `decCall` correctness.
-/

namespace Flapjack

theorem evalCrepFullCall_normal_returned_inversion_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (calleeContext : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceCalleeLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (caller : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (sourceBodyLocals sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceValues : List (PanValue α))
    (targetParameters : List Nat)
    (destinations : List Nat) (function : FunName)
    (arguments : List (CrepExp α)) (target : CrepState α)
    (hbodyCorrect : PanValueCrepProgramCorrect sourceBody)
    (hrelCallee : ∀ (parameters : List Nat) (body : CrepProg α)
      (calleeLocals : Nat → Option α),
      lookupCompiledFunction function functions = some (parameters, body) →
      ∀ values, assignCrepValues (fun _ => none) parameters values =
        some calleeLocals →
      panValueCrepStateRel structs calleeContext
        sourceCalleeLocals sourceGlobals sourceCalleeMemory
        { locals := calleeLocals, memory := caller.memory })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceCalleeMemory sourceBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hcall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
      (some (destinations, none)) function arguments = some (.normal target)) :
    ∃ values parameters body calleeLocals callee calleeValues callerLocals,
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress arguments = some values ∧
      lookupCompiledFunction function functions = some (parameters, body) ∧
      assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel
        { locals := calleeLocals, memory := caller.memory } body =
          some (.returned callee calleeValues) ∧
      assignCrepValues caller.locals destinations calleeValues =
        some callerLocals ∧
      target = { locals := callerLocals, memory := callee.memory } := by
  obtain hnormal | hreturned := evalCrepFullCall_normal_inversion
    functions crepPrimitive ffi sharedMem baseAddress topAddress targetFuel caller
    destinations function arguments target hcall
  · obtain ⟨values, parameters, body, calleeLocals, callee,
        hvalues, hlookup', hassign, hcallee, htarget⟩ := hnormal
    have hentry : (targetParameters, targetBody) = (parameters, body) := by
      exact Option.some.inj (hlookup.symm.trans hlookup')
    have htargetBody : targetBody = body := congrArg Prod.snd hentry
    have hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel
        { locals := calleeLocals, memory := caller.memory } targetBody =
        some (.normal callee) := by
      rw [htargetBody]
      exact hcallee
    exact False.elim (crepReturnedCall_normal_branch_impossible_of_body_correct
      calleeContext structs sourceFunctions functions sourceCalleeLocals sourceGlobals
      sourceCalleeMemory caller primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel sourceBody
      targetBody sourceBodyLocals sourceCalleeGlobals sourceValues
      calleeLocals callee hbodyCorrect
      (hrelCallee parameters body calleeLocals hlookup' values hassign)
      hsourceBody hcompileBody hcrepBody)
  · exact hreturned

end Flapjack
