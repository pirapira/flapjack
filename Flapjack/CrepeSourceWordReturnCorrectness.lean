import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeReturnCorrectness
import Flapjack.CrepeProgramReturnFuelRelation

/-!
The first program-level correctness bridge for the structural source-word
expression relation.  This packages expression compilation and evaluation
into the existing full-Crepe return theorem, leaving statement induction to
the following correctness slices.
-/

namespace Flapjack

theorem compile_full_pan_value_return_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (expression : SourceWordExp α) (value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 1
      sourceLocals sourceGlobals sourceMemory (.return expression.toExp) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 1 state
      (compileProg context (.return expression.toExp)) =
      some (.returned state [value]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
      (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals
    state.memory baseAddress topAddress bytesInWord hbytesInWord hlocals.2.1
    hlookup expression value hsource
  have hcompileShape : compileExp context expression.toExp =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiledList : evalCrepFullExps state.locals state.memory
      baseAddress topAddress [compiled] = some [value] := by
    simp [evalCrepFullExps, hcompiled]
  exact compile_full_pan_value_return_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord expression.toExp
    (.word value) [compiled] exceptionRel hsource
    (panValuePayloadWithinLimit_word structs value) hcompileShape hcompiledList hlocals

end Flapjack

namespace Flapjack

/-!
Stateful counterpart of the source-word return bridge.  The compatibility
theorem above remains unchanged; this wrapper transports the expression
witness through the explicit global-aware evaluator before invoking the
stateful return boundary.
-/

theorem compile_full_pan_value_return_source_word_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (expression : SourceWordExp α) (value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 1
      sourceLocals sourceGlobals sourceMemory (.return expression.toExp) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress 1 state
      (compileProg context (.return expression.toExp)) =
      some (.returned state [value]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
      (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_state_relation
    context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord hbytesInWord hlocals.2.1 hlookup
    expression value hsource
  have hcompileShape : compileExp context expression.toExp =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiledList : evalCrepFullExpsState state
      baseAddress topAddress [compiled] = some [value] := by
    simp [evalCrepFullExpsState, hcompiled]
  exact compile_full_pan_value_return_state_relation_fuel context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord 0 0 expression.toExp (.word value) [compiled] exceptionRel hsource
    (panValuePayloadWithinLimit_word structs value) hcompileShape hcompiledList
    hlocals

end Flapjack
