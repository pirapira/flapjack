import Flapjack.CrepeProgramReturnFuelRelation
import Flapjack.CrepeExpressionRelation

/-!
Source-word return correctness.

This theorem connects the scalar expression induction to the fuel-polymorphic
return boundary.  It is the reusable return case for localized Pancake
programs whose return expression belongs to the scalar Crep fragment.
-/

namespace Flapjack

theorem compile_full_pan_value_return_source_word_relation_fuel
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
    (expression : SourceWordExp α) (value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    ∃ compiled,
      compileExp context expression.toExp = ([compiled], .one) ∧
      evalCrepFullExp state.locals state.memory
        baseAddress topAddress compiled = some value ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord (sourceFuel + 1)
        sourceLocals sourceGlobals sourceMemory (.return expression.toExp) =
        some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (targetFuel + 1) state
        (compileProg context (.return expression.toExp)) =
        some (.returned state [value]) ∧
      panValueCrepControlRel structs context exceptionRel
        (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
        (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hrel.2.1 hlookup expression value hsource
  have hcompile' :
      compileExp context expression.toExp =
        ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiled' :
      evalCrepFullExps state.locals state.memory baseAddress topAddress
        [compiled] = some (panValueFlatWords (.word value)) := by
    simp [evalCrepFullExps, hcompiled, panValueFlatWords,
      panValueFlatWordsFuel]
  have hresult := compile_full_pan_value_return_relation_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel expression.toExp
    (.word value) [compiled] exceptionRel hsource
    (by simp) hcompile' hcompiled' hrel
  exact ⟨compiled, hcompile, hcompiled, hresult.1, hresult.2.1, hresult.2.2⟩

theorem compile_full_pan_value_return_source_word_state_relation_fuel
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
    (expression : SourceWordExp α) (value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    ∃ compiled,
      compileExp context expression.toExp = ([compiled], .one) ∧
      evalCrepFullExpsState state baseAddress topAddress [compiled] = some [value] ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord (sourceFuel + 1)
        sourceLocals sourceGlobals sourceMemory (.return expression.toExp) =
        some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
      evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (targetFuel + 1) state
        (compileProg context (.return expression.toExp)) =
        some (.returned state [value]) ∧
      panValueCrepControlRel structs context exceptionRel
        (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
        (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord hbytesInWord hrel.2.1 hlookup expression value hsource
  obtain ⟨compiled', hcompile', hnoGlobal⟩ := compileSourceWordExp_noGlobal
    context structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord hlookup expression value hsource
  have hcompiledEq : compiled = compiled' := by
    have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
      hcompile.symm.trans hcompile'
    exact (List.cons.inj (congrArg Prod.fst hpair)).1
  subst compiled'
  have hcompiledState :
      evalCrepFullExpsState state baseAddress topAddress [compiled] = some [value] := by
    have hcompat := evalCrepFullExpsState_eq_of_noGlobals state
      baseAddress topAddress [compiled]
      (by
        intro current hcurrent
        have hcurrent' : current = compiled := by simpa using hcurrent
        simpa [hcurrent'] using hnoGlobal)
    calc
      evalCrepFullExpsState state baseAddress topAddress [compiled] =
          evalCrepFullExps state.locals state.memory
            baseAddress topAddress [compiled] := hcompat
      _ = some [value] := by simp [evalCrepFullExps, hcompiled]
  have hcompileShape : compileExp context expression.toExp =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hresult := compile_full_pan_value_return_state_relation_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel expression.toExp
    (.word value) [compiled] exceptionRel hsource
    (by simp) hcompileShape
    (by simpa [panValueFlatWords, panValueFlatWordsFuel] using hcompiledState) hrel
  exact ⟨compiled, hcompile, hcompiledState, hresult.1, hresult.2.1, hresult.2.2⟩

end Flapjack
