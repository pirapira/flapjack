import Flapjack.CrepeDeclarationRelation

/-!
Fuel-polymorphic declaration binding for the source-to-Crep simulation.

The nested Crep declarations consume one target step per allocated slot, while
the source declaration consumes one outer step and evaluates its body at the
remaining source fuel.  Keeping these fuels independent is required by the
compositional program correctness predicate.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_dec_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (compiledValues : List (CrepExp α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompile : compileExp context value = (compiledValues, shape))
    (hlength : (allocatedNames context shape).length = compiledValues.length)
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord value = some sourceValue)
    (hshape : panShapeMatches (panValueShape structs sourceValue) shape = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceGlobals sourceMemory body = some sourceResult)
    (hcrep : CrepNestedDecsEval functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state (allocatedNames context shape)
      compiledValues
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) crepResult)
    (hdistinct : CrepDistinctNames (allocatedNames context shape))
    (hrel : panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.dec name shape value body) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (targetFuel + (allocatedNames context shape).length) state
      (compileProg context (.dec name shape value body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  have hcompileProg :
      compileProg context (.dec name shape value body) =
        nestedDecs (allocatedNames context shape) compiledValues
          (compileProg
            { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize shape }
            body) := by
    simp [compileProg, hcompile, hlength]
  have htarget := evalCrepFullProg_nestedDecs_of_eval
    functions crepPrimitive ffi sharedMem baseAddress topAddress targetFuel state
      (allocatedNames context shape) compiledValues
    (compileProg
      { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      body) crepResult hdistinct hcrep
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue,
      hshape, hsourceBody, restorePanValueControlLocal]
  constructor
  · exact htarget
  · exact hrel

end Flapjack
