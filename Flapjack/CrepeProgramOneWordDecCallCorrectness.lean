import Flapjack.CrepeDecCallIndependentFuelRelation
import Flapjack.CrepeProgramOneWordDeclarationControlRestoration
import Flapjack.CrepeProgramRelation

/-!
Compositional correctness for the normal-return path of a one-word
declaration call.

The callee simulation remains an explicit obligation: it must relate the
source call's returned value to the destination-aware Crep call state.  This
rule supplies the surrounding declaration machinery and applies recursive
correctness to the continuation body.
-/

namespace Flapjack

theorem panValueCrepDecCall_one_normal_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state callState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbody : PanValueCrepProgramCorrect body)
    (hrelBody : panValueCrepStateRel structs
      { context with
          vars := (name, (.one, allocatedNames context .one)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize .one }
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory callState)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hsourceShape : panShapeMatches
      (panValueShape structs sourceValue) .one = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body = some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context .one) }
      (some (allocatedNames context .one, none)) function compiledArguments =
      some (.normal callState))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) callState
      (compileProg
        { context with
            vars := (name, (.one, allocatedNames context .one)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize .one }
        body) = some crepResult)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name .one function arguments body) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 3) state
      (compileProg context (.decCall name .one function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) := by
  have hbodyRel := hbody
    { context with
        vars := (name, (.one, allocatedNames context .one)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize .one }
    structs sourceFunctions functions
    (updatePanValueMap sourceLocals name sourceValue)
    sourceCalleeGlobals sourceCalleeMemory callState
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel (targetFuel + 1)
    exceptionRel sourceResult crepResult hrelBody hsourceBody hcrepBody
  have hbodyRel' : panValueCrepControlRel structs
      { context with
          vars := (name, (.one, [context.maxVar + 1])) :: context.vars
          maxVar := context.maxVar + 1 }
      exceptionRel sourceResult crepResult := by
    simpa [allocatedNames, Shape.shapeSize, List.range, List.range.loop] using hbodyRel
  have houterRel := panValueCrepControlRel_restore_one_word_declaration
    structs context (sourceLocals name) state name hname hfresh exceptionRel
    sourceResult crepResult hbodyRel'
  have houterRel' : panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) := by
    simpa [allocatedNames, Shape.shapeSize, List.range, List.range.loop] using
      houterRel
  have hresult := compile_full_pan_value_decCall_relation_independent_fuel
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory state callState
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel none none none
    name .one function arguments body compiledArguments
    sourceCalleeGlobals sourceCalleeMemory sourceValue sourceResult crepResult
    exceptionRel hcompileArgs hsourceCall hsourceShape hsourceBody hcrepCall
    hcrepBody houterRel'
  refine ⟨hresult.1, ?_, hresult.2.2⟩
  simpa [allocatedNames, initializeCrepLocals,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult.2.1


theorem panValueCrepDecCall_one_normal_of_body_state_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state callState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hrelBody : panValueCrepStateRel structs
      { context with
          vars := (name, (.one, allocatedNames context .one)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize .one }
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory callState)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hsourceShape : panShapeMatches
      (panValueShape structs sourceValue) .one = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body = some sourceResult)
    (hcrepCall : evalCrepFullCallState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context .one) }
      (some (allocatedNames context .one, none)) function compiledArguments =
      some (.normal callState))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) callState
      (compileProg
        { context with
            vars := (name, (.one, allocatedNames context .one)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize .one }
        body) = some crepResult)
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      context.maxVar + 1 ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name .one function arguments body) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 3) state
      (compileProg context (.decCall name .one function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) := by
  have hbodyRel := hbody
    { context with
        vars := (name, (.one, allocatedNames context .one)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize .one }
    structs sourceFunctions functions
    (updatePanValueMap sourceLocals name sourceValue)
    sourceCalleeGlobals sourceCalleeMemory callState
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel (targetFuel + 1)
    exceptionRel sourceResult crepResult hrelBody hsourceBody hcrepBody
  have hbodyRel' : panValueCrepControlRel structs
      { context with
          vars := (name, (.one, [context.maxVar + 1])) :: context.vars
          maxVar := context.maxVar + 1 }
      exceptionRel sourceResult crepResult := by
    simpa [allocatedNames, Shape.shapeSize, List.range, List.range.loop] using hbodyRel
  have houterRel := panValueCrepControlRel_restore_one_word_declaration
    structs context (sourceLocals name) state name hname hfresh exceptionRel
    sourceResult crepResult hbodyRel'
  have houterRel' : panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context .one) crepResult) := by
    simpa [allocatedNames, Shape.shapeSize, List.range, List.range.loop] using
      houterRel
  have hresult := compile_full_pan_value_decCall_state_relation_independent_fuel
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory state callState
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel none none none
    name .one function arguments body compiledArguments
    sourceCalleeGlobals sourceCalleeMemory sourceValue sourceResult crepResult
    exceptionRel hcompileArgs hsourceCall hsourceShape hsourceBody hcrepCall
    hcrepBody houterRel'
  refine ⟨hresult.1, ?_, hresult.2.2⟩
  simpa [allocatedNames, initializeCrepLocals,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult.2.1


end Flapjack
