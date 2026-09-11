import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation

/-!
Fuel-polymorphic scalar raise lowering.

The source evaluates one word expression and raises it.  Crep evaluates the
same expression in a fresh temporary, spills that temporary to global address
zero, and raises the compiled exception code.  The raised control relation
records that reserved spill explicitly.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_raise_source_word_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (exception : ExceptionId) (exceptionCode value : α)
    (expression : SourceWordExp α)
    (compiled : CrepExp α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (_hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiled = some value)
    (hexception : exceptionRel exception (.word value) exceptionCode)
    (hfresh : state.locals (context.maxVar + 1) = none) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression.toExp) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.word value)) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 4) state
      (compileProg context (.raise exception expression.toExp)) =
      some (.raised
        { state with memory := updateMemory state.memory 0 value }
        exceptionCode) ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory exception (.word value)
      { state with memory := updateMemory state.memory 0 value }
      exceptionCode 0 := by
  have hcompileProg : compileProg context (.raise exception expression.toExp) =
      .seq
        (nestedDecs [context.maxVar + 1] [compiled]
          (crepNestedSeq (storeGlobals 0 context.bytesInWord
            [.var (context.maxVar + 1)])))
        (.raise exceptionCode) := by
    have hnames : freshNames context 1 1 =
        [context.maxVar + 1] := by
      simp [freshNames, List.range, List.range.loop]
    simp only [compileProg, hlookup, hcompile, Shape.shapeSize,
      List.length_cons, List.length_nil]
    rw [hnames]
    simp [nestedDecs, crepNestedSeq, storeGlobals]
  rw [hcompileProg]
  constructor
  · have hlimit : panValuePayloadWithinLimit structs (.word value) = true :=
      panValuePayloadWithinLimit_word structs value
    simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hlimit]
  constructor
  · have hrestore : restoreCrepLocal
        (updateCrepLocal state.locals (context.maxVar + 1) value)
        (context.maxVar + 1) none =
        state.locals := by
      funext current
      by_cases hcurrent : current = context.maxVar + 1
      · subst current
        simp [restoreCrepLocal, updateCrepLocal, hfresh]
      · simp [restoreCrepLocal, updateCrepLocal, hcurrent]
    simp [nestedDecs, crepNestedSeq, storeGlobals, evalCrepFullProg,
      evalCrepFullExp, hcompiled, hfresh, updateCrepLocal,
      restoreCrepResult, hrestore]
  · have hstate := panValueCrepRaisedStateRel_word_spill
      structs context sourceLocals sourceGlobals sourceMemory state 0 value hrel
    exact ⟨hstate, hexception⟩

end Flapjack
