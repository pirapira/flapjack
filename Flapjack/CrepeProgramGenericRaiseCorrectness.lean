import Flapjack.CrepeGlobalStoreCorrectness
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramAssignmentCorrectness
import Flapjack.CrepeAllocationNameLemmas

/-!
Generic structured-value Raise lowering.

This is the evaluator-facing part of the HOL Raise case: arbitrary flattened
values are evaluated into fresh temporaries, written to the compiler-owned
global area, and then raised with the looked-up exception code.  The separate
payload-observation theorem remains responsible for connecting that global
area to `globals_lookup` at the exact `pc_compile_correct` boundary.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_raise_state_relation_of_evidence
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
    (sourceFuel : Nat) (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception sourceValue) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode 0 := by
  let temporaries := freshNames context compiled.length 1
  let body := crepNestedSeq
    (storeGlobals 0 context.bytesInWord (temporaries.map (fun name => .var name)))
  let bodyState : CrepState α :=
    { state with locals := updateCrepLocalList state.locals temporaries values }
  let bodyResultState : CrepState α :=
    { bodyState with globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }
  let targetState : CrepState α :=
    { state with globals := updateMemoryListAt state.globals 0 context.bytesInWord values }
  have hvaluesLength : compiled.length = values.length :=
    evalCrepFullExpsState_length state baseAddress topAddress compiled values hcompiled
  have htemporaryLength : temporaries.length = values.length := by
    simp [temporaries, freshNames, hvaluesLength]
  have htemporaryDistinct : CrepDistinctNames temporaries := by
    exact crepDistinctNames_freshNames context compiled.length 1
  have hcompiledTemporaries : evalCrepFullExpsState bodyState
      baseAddress topAddress (temporaries.map (fun name => .var name)) =
      some values := by
    exact evalCrepFullExpsState_varList_updateCrepLocalList
      state baseAddress topAddress temporaries values htemporaryLength
      htemporaryDistinct
  have hbody := evalCrepFullProgState_storeGlobals_vars
    functions crepPrimitive ffi sharedMem baseAddress topAddress bodyState
    0 context.bytesInWord temporaries values htemporaryLength
    hcompiledTemporaries
  have hnested : CrepNestedDecsStateEval functions crepPrimitive ffi sharedMem
      baseAddress topAddress (values.length + 1) state temporaries compiled body
      (.normal bodyResultState) := by
    have hbody' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (values.length + 1) bodyState body =
        some (.normal bodyResultState) := by
      simpa [bodyState, bodyResultState, body] using hbody
    exact crepNestedDecsStateEval_of_evalExps_stable
      functions crepPrimitive ffi sharedMem baseAddress topAddress
      (values.length + 1) state temporaries compiled body (.normal bodyResultState)
      values (htemporaryLength.trans hvaluesLength.symm) hnot hcompiled hbody'
  have hnestedEval := evalCrepFullProgState_nestedDecs_of_eval
    functions crepPrimitive ffi sharedMem baseAddress topAddress
    (values.length + 1) state temporaries compiled body (.normal bodyResultState)
    htemporaryDistinct hnested
  have hrestoreLocals :
      restoredCrepLocals state.locals bodyState.locals temporaries =
        state.locals := by
    have hrestore : ∀ (locals : Nat → Option α) (names : List Nat)
        (values : List α), names.length = values.length →
        CrepDistinctNames names →
        (∀ name ∈ names, locals name = none) →
        restoredCrepLocals locals
          (updateCrepLocalList locals names values) names = locals := by
      intro locals names values hlength' hdistinct hnone
      induction names generalizing locals values with
      | nil =>
          cases values with
          | nil =>
              rfl
          | cons value values =>
              simp at hlength'
      | cons name names ih =>
          rcases hdistinct with ⟨hnotName, htailDistinct⟩
          cases values with
          | nil => simp at hlength'
          | cons value values =>
              have hlengthTail : names.length = values.length := by
                simpa using Nat.succ.inj hlength'
              have hnoneTail : ∀ current ∈ names,
                  updateCrepLocal locals name value current = none := by
                intro current hcurrent
                have hcurrentNe : current ≠ name := by
                  intro heq
                  apply hnotName
                  simpa [heq] using hcurrent
                have hnoneCurrent : locals current = none :=
                  hnone current (by simp [hcurrent])
                simp [updateCrepLocal, hcurrentNe, hnoneCurrent]
              have htail := ih
                (locals := updateCrepLocal locals name value)
                (values := values) hlengthTail htailDistinct
                (by
                  intro current hcurrent
                  exact hnoneTail current hcurrent)
              funext current
              by_cases hcurrent : current = name
              · simp [restoredCrepLocals, updateCrepLocal,
                  updateCrepLocalList, hcurrent]
              · simp only [restoredCrepLocals, hcurrent,
                  updateCrepLocalList]
                have hinv : ∀ (tailNames : List Nat), name ∉ tailNames →
                    restoredCrepLocals
                        (updateCrepLocal locals name value)
                        (updateCrepLocalList
                        (updateCrepLocal locals name value) names values)
                        tailNames current =
                      restoredCrepLocals locals
                        (updateCrepLocalList
                        (updateCrepLocal locals name value) names values)
                        tailNames current := by
                  intro tailNames
                  induction tailNames with
                  | nil =>
                      intro _
                      rfl
                  | cons tailName tailNames ihTail =>
                      intro hname
                      by_cases htail : current = tailName
                      · have htailNe : tailName ≠ name := by
                          intro heq
                          apply hname
                          simp [heq]
                        simp [restoredCrepLocals, htail, updateCrepLocal,
                          htailNe]
                      · have htail' : name ∉ tailNames := by
                          intro hmem
                          apply hname
                          exact List.mem_cons_of_mem tailName hmem
                        simp [restoredCrepLocals, htail,
                          ihTail htail', updateCrepLocal, hcurrent, htail']
                have htailCurrent := congrFun htail current
                rw [hinv names hnotName] at htailCurrent
                change restoredCrepLocals locals
                  (updateCrepLocalList
                    (updateCrepLocal locals name value) names values)
                  names current = locals current
                rw [htailCurrent]
                simp [updateCrepLocal, hcurrent]
    exact hrestore state.locals temporaries values htemporaryLength
      htemporaryDistinct (by
        intro name hmem
        exact hfresh name (by simpa [temporaries] using hmem))
  have hrestored : restoreCrepResultList state.locals temporaries
      (.normal bodyResultState) = .normal targetState := by
    have hrestored' := restoreCrepResultList_normal_explicit
      state.locals bodyState.locals bodyState.memory temporaries
      bodyResultState.globals
    rw [hrestoreLocals] at hrestored'
    simpa [bodyResultState, bodyState, targetState] using hrestored'
  have hnestedEval' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + 1 + temporaries.length) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [hrestored] using hnestedEval
  have hcompileProg : compileProg context (.raise exception expression) =
      .seq (nestedDecs temporaries compiled body) (.raise exceptionCode) := by
    simp only [compileProg, hlookup, hcompile, hlength, temporaries, body]
    rfl
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · rw [hcompileProg]
    change evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress ((values.length + temporaries.length + 1) + 1) state
      (.seq (nestedDecs temporaries compiled body) (.raise exceptionCode)) = _
    have hnestedEval'' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress (values.length + temporaries.length + 1) state
        (nestedDecs temporaries compiled body) =
        some (.normal targetState) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval'
    simp [evalCrepFullProgState, hnestedEval'', targetState]
  · have hstate : panValueCrepRaisedStateRel structs context
        sourceGlobals sourceMemory targetState 0 := by
      refine ⟨?_, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
      · exact hrel.1
      · intro address _
        exact congrFun hrel.2.2 address
    exact ⟨hstate, hexception⟩

end Flapjack
