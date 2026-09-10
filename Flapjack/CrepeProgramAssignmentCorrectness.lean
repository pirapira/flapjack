import Flapjack.CrepeProgramAssignmentFuelRelation
import Flapjack.CrepeProgramRelation

/-!
The local-assignment constructor for the compositional Pancake-to-Crep
correctness predicate.

The compiler has two lowerings for a one-word assignment: a direct assignment
when the destination is not read by the expression, and a temporary
declaration otherwise.  The semantic invariants needed by the latter are
kept explicit here.  They are the Lean counterparts of the source proof's
fresh-slot and non-overlap obligations.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_assign_local_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hnoalias : ∀ (context : CompileContext α) (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        slot ∉ oldSlots)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hslotFresh : ∀ (context : CompileContext α) (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      context.maxVar + 1 ≠ slot) :
    PanValueCrepProgramCorrect (.assign .local name expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      have hsourceInfo : ∃ oldValue value,
          sourceLocals name = some (.word oldValue) ∧
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord expression.toExp =
            some (.word value) := by
        cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
            sourceMemory baseAddress topAddress bytesInWord expression.toExp with
        | none =>
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
        | some sourceValue =>
            obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
              structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
              bytesInWord context hrel.2.1
              (fun current currentValue hcurrent =>
                hlookup context sourceLocals current currentValue hcurrent)
              expression sourceValue hvalue
            have hsourceValue : some sourceValue = some (.word value) :=
              congrArg some hword
            have hsource' := hsource
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hword] at hsource'
            have hlocal : ∃ oldValue,
                sourceLocals name = some (.word oldValue) := by
              cases hlocal : sourceLocals name with
              | none =>
                  simp [panValueAssignmentValid, hlocal] at hsource'
              | some oldValue =>
                  cases oldValue with
                  | word oldValue =>
                      exact ⟨oldValue, by simp [hlocal]⟩
                  | rStruct fields =>
                      simp [panValueAssignmentValid, hlocal,
                        panValueShape, panShapeMatches] at hsource'
                  | nStruct oldName fields =>
                      simp [panValueAssignmentValid, hlocal,
                        panValueShape, panShapeMatches] at hsource'
            obtain ⟨oldValue, hold⟩ := hlocal
            exact ⟨oldValue, value, hold, hsourceValue⟩
      rcases hsourceInfo with ⟨oldValue, value, hold, hsourceValue⟩
      obtain ⟨slot, hslot⟩ :=
        hlookup context sourceLocals name (.word oldValue) hold
      obtain ⟨compiled, hcompile, hcompiled⟩ :=
        compileSourceWordExp_relation context structs sourceLocals sourceGlobals
          sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
          (hbytesInWord context bytesInWord) hrel.2.1
          (fun current currentValue hcurrent => by
            obtain ⟨currentSlot, hcurrentSlot⟩ :=
              hlookup context sourceLocals current currentValue hcurrent
            exact ⟨currentSlot, hcurrentSlot⟩)
          expression value hsourceValue
      have hnoalias' := hnoalias context slot hslot
      by_cases hdistinct : distinctLists [slot] (crepExpVars compiled) = true
      · cases targetFuel with
        | zero =>
            simp [compileProg, hslot, hcompile, hdistinct,
              crepNestedSeq, evalCrepFullProg] at hcrep
        | succ targetFuel =>
            cases targetFuel with
            | zero =>
                simp [compileProg, hslot, hcompile, hdistinct,
                  crepNestedSeq, evalCrepFullProg] at hcrep
            | succ targetFuel =>
                have hresult :=
                  compile_full_pan_value_local_assign_source_word_relation_fuel
                    context structs sourceFunctions functions sourceLocals sourceGlobals
                    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                    baseAddress topAddress bytesInWord sourceFuel targetFuel name slot
                    oldValue value expression compiled hslot hold hsourceValue hcompile
                    hcompiled hdistinct hrel hnoalias'
                have hcrepEq :
                    CrepControlResult.normal
                        { state with locals := updateCrepLocal state.locals slot value } =
                      crepResult := by
                  exact Option.some.inj (hresult.2.1.symm.trans hcrep)
                have hsourceEq :=
                  Option.some.inj (hresult.1.symm.trans hsource)
                cases hsourceEq
                cases hcrepEq
                exact hresult.2.2
      · have hnotDistinct : distinctLists [slot] (crepExpVars compiled) = false := by
          simpa using hdistinct
        have htemporary : state.locals (context.maxVar + 1) = none :=
          hfresh context state
        have htemporaryNe : context.maxVar + 1 ≠ slot :=
          hslotFresh context slot hslot
        cases targetFuel with
        | zero =>
            simp [compileProg, hslot, hcompile, hnotDistinct, freshNames,
              nestedDecs, crepNestedSeq, evalCrepFullProg] at hcrep
        | succ targetFuel =>
            cases targetFuel with
            | zero =>
                simp [compileProg, hslot, hcompile, hnotDistinct, freshNames,
                  nestedDecs, crepNestedSeq, evalCrepFullProg] at hcrep
            | succ targetFuel =>
                cases targetFuel with
                | zero =>
                    simp [compileProg, hslot, hcompile, hnotDistinct, freshNames,
                      nestedDecs, crepNestedSeq, evalCrepFullProg] at hcrep
                | succ targetFuel =>
                    have hresult :=
                      compile_full_pan_value_local_assign_source_word_temporary_relation_fuel
                        context structs sourceFunctions functions sourceLocals sourceGlobals
                        sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                        baseAddress topAddress bytesInWord sourceFuel targetFuel name slot
                        (context.maxVar + 1) oldValue value expression compiled hslot hold
                        hsourceValue hcompile hcompiled hnotDistinct rfl htemporary
                        htemporaryNe hrel hnoalias'
                    have hcrepEq :
                        CrepControlResult.normal
                            { state with locals := updateCrepLocal state.locals slot value } =
                          crepResult := by
                      exact Option.some.inj (hresult.2.1.symm.trans hcrep)
                    have hsourceEq :=
                      Option.some.inj (hresult.1.symm.trans hsource)
                    cases hsourceEq
                    cases hcrepEq
                    exact hresult.2.2

end Flapjack
