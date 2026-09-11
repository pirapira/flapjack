import Flapjack.CrepeDeclarationExpressionAdapter
import Flapjack.CrepeProgramDeclarationGeneralCorrectness

/-!
Declaration correctness with the universal expression contract.  The
declaration constructor still receives the static-context facts that are
specific to allocated names and freshness, but expression evaluation and
flattening are now supplied by `PanValueCrepExpressionCorrect`.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_dec_of_expression_contract
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hname : ∀ (context : CompileContext α),
      lookupInfo name context.vars = none)
    (hfresh : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ allocatedNames context shape →
        temporary ∉ oldSlots)
    (hcompiledFresh : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)),
      ∀ temporary, temporary ∈ allocatedNames context shape →
        ∀ expression ∈ compiled, temporary ∉ crepExpVars expression)
    (hcompile : ∀ (context : CompileContext α),
      ∃ compiledValues,
        compileExp context value = (compiledValues, shape) ∧
        (allocatedNames context shape).length = compiledValues.length)
    (hshape : ∀ (_context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α),
      ∃ sourceValue,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord value = some sourceValue ∧
        panShapeMatches (panValueShape structs sourceValue) shape = true)
    (hvalue : PanValueCrepExpressionCorrect value)
    (hdistinct : ∀ (context : CompileContext α),
      CrepDistinctNames (allocatedNames context shape)) :
    PanValueCrepProgramCorrect (.dec name shape value body) := by
  have hcompiledEval : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α)
      (compiledValues : List (CrepExp α)) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      compileExp context value = (compiledValues, shape) →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord value = some sourceValue →
      ∃ values,
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiledValues = some values ∧
        compiledValues.length = values.length ∧
        panValueFlatWords sourceValue = values := by
    intro context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord compiledValues sourceValue hrel
      hcompileValue hsource
    exact panValueCrepExpressionCorrect_compiled_list value hvalue context structs
      sourceLocals sourceGlobals sourceMemory state baseAddress topAddress
      bytesInWord compiledValues shape sourceValue hrel hcompileValue hsource
  exact panValueCrepProgramCorrect_dec_general name shape value body hbody hname
    hfresh hcompiledFresh hcompile hshape hcompiledEval hdistinct

end Flapjack
