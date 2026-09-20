import Flapjack.CrepeGlobalStoreCorrectness
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeExpressionListRelation
import Flapjack.CrepeProgramAssignmentCorrectness
import Flapjack.CrepeAllocationNameLemmas
import Flapjack.CrepeDeclarationFuelInversion

/-!
Generic structured-value Raise lowering.

This is the evaluator-facing part of the HOL Raise case: arbitrary flattened
values are evaluated into fresh temporaries, written to the compiler-owned
global area, and then raised with the looked-up exception code.  The separate
payload-observation theorem remains responsible for connecting that global
area to `globals_lookup` at the exact `pc_compile_correct` boundary.
-/

namespace Flapjack

/-! A successful global-store sequence necessarily has enough target fuel for
    one evaluator step per stored word and its terminating `skip`.  The
    forward store theorem below deliberately accepts excess fuel; this
    converse is the fuel inversion needed when a program-correctness
    constructor starts from an arbitrary successful target evaluation. -/
theorem evalCrepFullProgState_storeGlobals_vars_fuel_lower_bound
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (address stride : α) (names : List Nat) (values : List α)
    (result : CrepControlResult α)
    (hlength : names.length = values.length)
    (hvalues : evalCrepFullExpsState state baseAddress topAddress
      (names.map (fun name => .var name)) = some values)
    (hresult : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress fuel state
      (crepNestedSeq (storeGlobals address stride
        (names.map (fun name => .var name)))) = some result) :
    values.length + 1 ≤ fuel := by
  induction names generalizing fuel state address values result with
  | nil =>
      cases values with
      | nil =>
          cases fuel with
          | zero => simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
          | succ fuel =>
              simp only [List.length_nil, Nat.zero_add]
              exact Nat.succ_le_succ (Nat.zero_le fuel)
      | cons value values =>
          simp at hlength
  | cons name names ih =>
      cases values with
      | nil =>
          simp at hlength
      | cons value values =>
          cases fuel with
          | zero =>
              simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
              | succ fuel =>
                  simp only [List.map_cons, evalCrepFullExpsState] at hvalues
                  cases hname : evalCrepFullExpState state baseAddress topAddress
                      (.var name) with
                  | none =>
                      simp [hname] at hvalues
                  | some nameValue =>
                      cases htail : evalCrepFullExpsState state baseAddress topAddress
                          (names.map (fun name => .var name)) with
                      | none =>
                          simp [hname, htail] at hvalues
                      | some tailValues =>
                          have hpair : nameValue :: tailValues = value :: values :=
                            Option.some.inj (by simpa [hname, htail] using hvalues)
                          cases hpair
                          have hlength' : names.length = values.length := by
                            exact Nat.succ.inj hlength
                          let nextState : CrepState α :=
                            { state with globals := updateMemory state.globals address value }
                          have htailEval' :
                              evalCrepFullExpsState nextState baseAddress topAddress
                                (names.map (fun name => .var name)) = some values := by
                            have hvars : ∀ (current : CrepState α),
                                current.locals = state.locals →
                                ∀ (currentNames : List Nat),
                                evalCrepFullExpsState current baseAddress topAddress
                                    (currentNames.map (fun name => .var name)) =
                                  evalCrepFullExpsState state baseAddress topAddress
                                    (currentNames.map (fun name => .var name)) := by
                              intro current hlocals currentNames
                              induction currentNames with
                              | nil => simp [evalCrepFullExpsState]
                              | cons currentName currentNames ih =>
                                  simp [evalCrepFullExpsState, evalCrepFullExpState,
                                    ih, hlocals]
                            rw [hvars nextState rfl]
                            exact htail
                          cases htailResult : evalCrepFullProgState functions primitive
                              ffi sharedMem baseAddress topAddress (fuel + 1) nextState
                              (crepNestedSeq (storeGlobals (address + stride) stride
                                (names.map (fun name => .var name)))) with
                          | none =>
                              simp [crepNestedSeq, storeGlobals, evalCrepFullProgState,
                                hname, htailResult, nextState] at hresult
                          | some tailResult =>
                              have htailBound := ih (fuel := fuel + 1)
                                (state := nextState)
                                (address := address + stride) (values := values)
                                (result := tailResult) hlength' htailEval' htailResult
                              simp only [List.length_cons] at ⊢
                              omega

theorem evalPanValueExp_nStruct_of_fields_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (name : StructName) (fields : List (FieldName × Exp α))
    (values : List (FieldName × PanValue α))
    (info : StructInfo)
    (hlookup : lookupInfo name structs = some info)
    (hfields : evalPanValueExp.evalPanValueFields structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord fields = some values)
    (hshape : panValueFieldsHaveShapes structs info.fields values = true) :
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.nStruct name fields) =
      some (.nStruct name values) := by
  simp [evalPanValueExp, hlookup, hfields, hshape]

theorem evalPanValueExp_structPass_of_named_fields_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (sourceStructs postStructs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (name : StructName) (fields : List (FieldName × Exp α))
    (values : List (FieldName × PanValue α))
    (info : StructInfo)
    (postExpression : Exp α) (postValue : PanValue α)
    (hlookup : lookupInfo name sourceStructs = some info)
    (hfields : evalPanValueExp.evalPanValueFields sourceStructs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord fields = some values)
    (hshape : panValueFieldsHaveShapes sourceStructs info.fields values = true)
    (hpass : ∀ namedValue,
      evalPanValueExp sourceStructs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord (.nStruct name fields) = some namedValue →
      evalPanValueExp postStructs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord postExpression = some postValue) :
    evalPanValueExp postStructs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord postExpression = some postValue := by
  apply hpass (.nStruct name values)
  exact evalPanValueExp_nStruct_of_fields_evidence sourceStructs sourceLocals sourceGlobals
    sourceMemory baseAddress topAddress bytesInWord name fields values info
    hlookup hfields hshape

theorem evalCrepFullProgState_raise_of_evidence_of_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (compiled : List (CrepExp α)) (shape : Shape)
    (values : List α) (extraFuel : Nat)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2 + extraFuel)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  let temporaries := freshNames context compiled.length 1
  let body := crepNestedSeq
    (storeGlobals 0 context.bytesInWord (temporaries.map (fun name => .var name)))
  let bodyState : CrepState α :=
    { state with locals := updateCrepLocalList state.locals temporaries values }
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
  have hbody := evalCrepFullProgState_storeGlobals_vars_of_fuel
    functions primitive ffi sharedMem baseAddress topAddress
    (values.length + 1 + extraFuel) bodyState 0 context.bytesInWord
    temporaries values (by omega) htemporaryLength hcompiledTemporaries
  have hbody' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (values.length + 1 + extraFuel) bodyState body =
      some (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) := by
    simpa [body] using hbody
  have hnested : CrepNestedDecsStateEval functions primitive ffi sharedMem
      baseAddress topAddress (values.length + 1 + extraFuel) state temporaries
      compiled body (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) := by
    exact crepNestedDecsStateEval_of_evalExps_stable
      functions primitive ffi sharedMem baseAddress topAddress
      (values.length + 1 + extraFuel) state temporaries compiled body
      (.normal { bodyState with
        globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values })
      values (htemporaryLength.trans hvaluesLength.symm) hnot hcompiled hbody'
  have hnestedEval := evalCrepFullProgState_nestedDecs_of_eval
    functions primitive ffi sharedMem baseAddress topAddress
    (values.length + 1 + extraFuel) state temporaries compiled body
    (.normal { bodyState with
      globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values })
    htemporaryDistinct hnested
  have hrestoreLocals :
      restoredCrepLocals state.locals bodyState.locals temporaries =
        state.locals := by
    exact restoredCrepLocals_updateCrepLocalList state.locals temporaries values
      htemporaryLength htemporaryDistinct (by
        intro name hmem
        exact hfresh name (by simpa [temporaries] using hmem))
  have hnestedEval' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + 1 + extraFuel + temporaries.length) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    have hrestored : restoreCrepResultList state.locals temporaries
        (.normal { bodyState with
          globals := updateMemoryListAt bodyState.globals 0 context.bytesInWord values }) =
        .normal targetState := by
      have hrestored' := restoreCrepResultList_normal_explicit
        state.locals bodyState.locals bodyState.memory temporaries
        (updateMemoryListAt bodyState.globals 0 context.bytesInWord values)
      rw [hrestoreLocals] at hrestored'
      simpa [bodyState, targetState] using hrestored'
    simpa [hrestored] using hnestedEval
  have hcompileProg : compileProg context (.raise exception expression) =
      .seq (nestedDecs temporaries compiled body) (.raise exceptionCode) := by
    simp only [compileProg, hlookup, hcompile, hlength, temporaries, body]
    rfl
  rw [hcompileProg]
  change evalCrepFullProgState functions primitive ffi sharedMem
    baseAddress topAddress
    ((values.length + temporaries.length + 1) + 1 + extraFuel) state
    (.seq (nestedDecs temporaries compiled body) (.raise exceptionCode)) = _
  have hnestedEval'' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + temporaries.length + 1 + extraFuel) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval'
  have hfuel : values.length + temporaries.length + 2 + extraFuel =
      (values.length + temporaries.length + 1 + extraFuel) + 1 := by omega
  rw [hfuel]
  have hsecondFuel : values.length + temporaries.length + 1 + extraFuel =
      (values.length + temporaries.length + extraFuel) + 1 := by omega
  rw [hsecondFuel]
  have hnestedEval''' : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (values.length + temporaries.length + extraFuel + 1) state
      (nestedDecs temporaries compiled body) = some (.normal targetState) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnestedEval''
  simp [evalCrepFullProgState, hnestedEval''', targetState]

theorem evalCrepFullProgState_storeGlobals_vars_inv
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat) (state : CrepState α)
    (address stride : α) (names : List Nat) (values : List α)
    (result : CrepControlResult α)
    (hlength : names.length = values.length)
    (hvalues : evalCrepFullExpsState state baseAddress topAddress
      (names.map (fun name => .var name)) = some values)
    (hresult : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (crepNestedSeq (storeGlobals address stride
        (names.map (fun name => .var name)))) = some result) :
    result = .normal { state with
      globals := updateMemoryListAt state.globals address stride values } := by
  induction names generalizing state address values targetFuel result with
  | nil =>
      cases values with
      | nil =>
          cases targetFuel with
          | zero =>
              simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
          | succ targetFuel =>
              simpa [crepNestedSeq, storeGlobals, evalCrepFullProgState,
                updateMemoryListAt] using hresult.symm
      | cons value values =>
          simp at hlength
  | cons name names ih =>
      cases values with
      | nil =>
          simp at hlength
      | cons value values =>
          cases targetFuel with
          | zero =>
              simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [crepNestedSeq, storeGlobals, evalCrepFullProgState] at hresult
              | succ targetFuel =>
                  simp only [List.map_cons, evalCrepFullExpsState] at hvalues
                  cases hname : evalCrepFullExpState state baseAddress topAddress
                      (.var name) with
                  | none =>
                      simp [hname] at hvalues
                  | some nameValue =>
                      cases htail : evalCrepFullExpsState state baseAddress topAddress
                          (names.map (fun name => .var name)) with
                      | none =>
                          simp [hname, htail] at hvalues
                      | some tailValues =>
                          have hpair : nameValue :: tailValues = value :: values :=
                            Option.some.inj (by simpa [hname, htail] using hvalues)
                          cases hpair
                          have hlength' : names.length = values.length := by
                            exact Nat.succ.inj hlength
                          have htailEval :
                              evalCrepFullExpsState state baseAddress topAddress
                                (names.map (fun name => .var name)) = some values := by
                            exact htail
                          have hnameEval : evalCrepFullExpState state
                              baseAddress topAddress (.var name) = some value := by
                            exact hname
                          let nextState : CrepState α :=
                            { state with globals := updateMemory state.globals address value }
                          have htailEval' :
                              evalCrepFullExpsState nextState baseAddress topAddress
                                (names.map (fun name => .var name)) = some values := by
                            have hvars : ∀ (current : CrepState α),
                                current.locals = state.locals →
                                ∀ (currentNames : List Nat),
                                evalCrepFullExpsState current baseAddress topAddress
                                    (currentNames.map (fun name => .var name)) =
                                  evalCrepFullExpsState state baseAddress topAddress
                                    (currentNames.map (fun name => .var name)) := by
                              intro current hlocals currentNames
                              induction currentNames with
                              | nil => simp [evalCrepFullExpsState]
                              | cons currentName currentNames ih =>
                                  simp [evalCrepFullExpsState, evalCrepFullExpState,
                                    ih, hlocals]
                            rw [hvars nextState rfl]
                            exact htailEval
                          cases htailResult : evalCrepFullProgState functions primitive
                              ffi sharedMem baseAddress topAddress (targetFuel + 1)
                              nextState
                              (crepNestedSeq (storeGlobals (address + stride) stride
                                (names.map (fun name => .var name)))) with
                          | none =>
                              have hresult' :
                                  evalCrepFullProgState functions primitive ffi
                                    sharedMem baseAddress topAddress (targetFuel + 1)
                                    nextState
                                    (crepNestedSeq (storeGlobals (address + stride)
                                      stride (names.map (fun name => .var name)))) =
                                  some result := by
                                simpa [crepNestedSeq, storeGlobals,
                                  evalCrepFullProgState, hnameEval, nextState] using
                                  hresult
                              rw [htailResult] at hresult'
                              simp at hresult'
                          | some tailResult =>
                              have htailEq : tailResult = result := by
                                have hresult' :
                                    evalCrepFullProgState functions primitive ffi
                                      sharedMem baseAddress topAddress (targetFuel + 1)
                                      nextState
                                      (crepNestedSeq (storeGlobals (address + stride)
                                        stride (names.map (fun name => .var name)))) =
                                    some result := by
                                  simpa [crepNestedSeq, storeGlobals,
                                    evalCrepFullProgState, hnameEval, nextState] using
                                    hresult
                                rw [htailResult] at hresult'
                                exact Option.some.inj hresult'
                              have htailInv := ih
                                (state := nextState) (address := address + stride)
                                (values := values) (targetFuel := targetFuel + 1)
                                (result := tailResult) hlength' htailEval' htailResult
                              cases htailEq
                              simpa [nextState, updateMemoryListAt, Nat.add_assoc] using
                                htailInv

theorem panValueCrepProgramStateCorrect_raise_word_list_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (values : List α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α)
      (name : Nat), name ∈ freshNames context values.length 1 →
      state.locals name = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct (values.map PanValue.word)) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct (values.map (fun value => .const value)))) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceExps :
          ∀ values : List α,
          evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
            sourceMemory baseAddress topAddress bytesInWord
            (values.map (fun value => .const value)) =
          some (values.map PanValue.word) := by
        intro values
        induction values with
        | nil => simp [evalPanValueExp.evalPanValueExps]
        | cons value values ih =>
            simp only [List.map_cons]
            simp [evalPanValueExp.evalPanValueExps, evalPanValueExp]
            rw [ih]
            rfl
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct (values.map (fun value => .const value))) =
          some (.rStruct (values.map PanValue.word)) := by
        simp only [evalPanValueExp]
        rw [hsourceExps values]
        rfl
      have hcompileExpList : ∀ values : List α,
          compileExp.compileExpList context
            (values.map (fun value => .const value)) =
          values.map (fun value => ([.const value], .one)) := by
        intro values
        induction values with
        | nil => simp [compileExp.compileExpList]
        | cons value values ih =>
            simp [compileExp.compileExpList, compileExp, ih]
      have hflatCompilePairs : ∀ values : List α,
          List.flatMap Prod.fst
              (values.map (fun value => ([CrepExp.const value], Shape.one))) =
            values.map (fun value => .const value) := by
        intro values
        induction values with
        | nil => rfl
        | cons value values ih => simp [ih]
      have hcompile :
          compileExp context
              (.rStruct (values.map (fun value => .const value))) =
            (values.map (fun value => .const value),
              .comb (values.map (fun _ => .one))) := by
        simp [compileExp, hcompileExpList, hflatCompilePairs,
          Function.comp_def]
      have hcompiled :
          ∀ values : List α,
          evalCrepFullExpsState state baseAddress topAddress
            (values.map (fun value => .const value)) = some values := by
        intro values
        induction values with
        | nil => simp [evalCrepFullExpsState]
        | cons value values ih =>
            simp only [List.map_cons]
            simp [evalCrepFullExpsState, evalCrepFullExpState]
            rw [ih]
            rfl
      have hvaluesLength :
          (values.map (fun value => (CrepExp.const value))).length = values.length := by
        simp
      have hlengthList : ∀ values : List α,
          (values.map (fun value => (CrepExp.const value))).length =
            Shape.shapeSize (.comb (values.map (fun _ => Shape.one))) := by
        intro values
        have hfold : ∀ (start : Nat) (values : List α),
            List.foldl (fun total field => total + field.shapeSize) start
              (values.map (fun _ => Shape.one)) = start + values.length := by
          intro start values
          induction values generalizing start with
          | nil => simp
          | cons value values ih =>
              simp [ih, Nat.add_comm] <;> omega
        simp [Shape.shapeSize, hfold]
      have hlength := hlengthList values
      have hnot : ∀ name ∈ freshNames context
          (values.map (fun value => (CrepExp.const value))).length 1,
          ∀ expression ∈
            (values.map (fun value => (CrepExp.const value)) : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        intro name hname expression hexpression
        obtain ⟨value, _, rfl⟩ := List.mem_map.1 hexpression
        simp
      have hfresh' : ∀ name ∈ freshNames context
          (values.map (fun value => (CrepExp.const value))).length 1,
          state.locals name = none := by
        intro name hname
        apply hfresh context state name
        simpa [hvaluesLength] using hname
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct (values.map PanValue.word)) = true := by
        have hsource' := hsource
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue] at hsource'
        exact hsource'.1
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hsourceEq : sourceResult =
          .raised (fun _ => none) sourceGlobals sourceMemory exception
            (.rStruct (values.map PanValue.word)) := by
        have hsource' := hsource
        simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue, hvalid]
          at hsource'
        exact hsource'.symm
      let temporaries := freshNames context
        (values.map (fun value => (CrepExp.const value))).length 1
      let body := crepNestedSeq
        (storeGlobals 0 context.bytesInWord
          (temporaries.map (fun name => .var name)))
      have htemporaryLength : temporaries.length = values.length := by
        simp [temporaries, freshNames, hvaluesLength]
      have htemporaryCompiledLength : temporaries.length =
          (values.map (fun value => (CrepExp.const value))).length := by
        simp [temporaries, freshNames]
      have htemporaryDistinct : CrepDistinctNames temporaries := by
        exact crepDistinctNames_freshNames context
          (values.map (fun value => (CrepExp.const value))).length 1
      have hcompileProg :
          compileProg context
              (.raise exception
                (.rStruct (values.map (fun value => .const value)))) =
            .seq
              (nestedDecs temporaries
                (values.map (fun value => .const value)) body)
              (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength, temporaries,
          freshNames, Shape.shapeSize, body]
      rw [hcompileProg] at hcrep
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hfirst : evalCrepFullProgState functions crepPrimitive ffi sharedMem
              baseAddress topAddress targetFuel state
              (nestedDecs temporaries
                (values.map (fun value => .const value)) body) with
          | none =>
              simp [evalCrepFullProgState, hfirst] at hcrep
          | some firstResult =>
              obtain ⟨bodyFuel, bodyResult, hbodyFuel, hnested, hrestore⟩ :=
                crepNestedDecsStateEval_of_eval
                  functions crepPrimitive ffi sharedMem baseAddress topAddress
                  targetFuel state temporaries
                  (values.map (fun value => .const value)) body firstResult
                  htemporaryDistinct htemporaryCompiledLength hfirst
              have hbodyEval := crepNestedDecsStateEval_body_of_evalExps_stable
                functions crepPrimitive ffi sharedMem baseAddress topAddress
                bodyFuel state temporaries
                (values.map (fun value => .const value)) body bodyResult values
                htemporaryCompiledLength hnot (hcompiled values) hnested
              have hbodyValues := evalCrepFullExpsState_varList_updateCrepLocalList
                state baseAddress topAddress temporaries values htemporaryLength
                htemporaryDistinct
              have hbodyNormal := evalCrepFullProgState_storeGlobals_vars_inv
                functions crepPrimitive ffi sharedMem baseAddress topAddress
                bodyFuel
                { state with locals :=
                    (updateCrepLocalList state.locals temporaries values) }
                0 context.bytesInWord temporaries values bodyResult
                (by simpa using htemporaryLength) hbodyValues hbodyEval
              have hrestoreLocals :
                  restoredCrepLocals state.locals
                      (updateCrepLocalList state.locals temporaries values)
                      temporaries = state.locals := by
                exact restoredCrepLocals_updateCrepLocalList state.locals
                  temporaries values htemporaryLength htemporaryDistinct
                  (by
                    intro name hmem
                    exact hfresh context state name
                      (by simpa [temporaries] using hmem))
              have hrestored :
                  restoreCrepResultList state.locals temporaries
                      (.normal { state with
                        locals := updateCrepLocalList state.locals temporaries values
                        globals := updateMemoryListAt state.globals 0
                          context.bytesInWord values }) =
                    .normal { state with
                      globals := updateMemoryListAt state.globals 0
                        context.bytesInWord values } := by
                have hrestored' := restoreCrepResultList_normal_explicit
                  state.locals
                  (updateCrepLocalList state.locals temporaries values)
                  state.memory temporaries
                  (updateMemoryListAt state.globals 0 context.bytesInWord values)
                rw [hrestoreLocals] at hrestored'
                exact hrestored'
              have hfirstNormal : firstResult = .normal
                  { state with globals :=
                      (updateMemoryListAt state.globals 0 context.bytesInWord values) } := by
                rw [hbodyNormal] at hrestore
                rw [hrestored] at hrestore
                exact hrestore.symm
              cases targetFuel with
              | zero =>
                  simp [evalCrepFullProgState, hfirst, hfirstNormal] at hcrep
              | succ targetFuel =>
                  simp [evalCrepFullProgState, hfirst, hfirstNormal] at hcrep
                  have hcrepEq := hcrep
                  cases hsourceEq
                  cases hcrepEq
                  have hstate : panValueCrepRaisedStateRel structs context
                      sourceGlobals sourceMemory
                      { state with globals :=
                          (updateMemoryListAt state.globals 0
                            context.bytesInWord values) } 0 := by
                    refine ⟨hrel.1,
                      panValueCrepLocalsRel_empty structs context state.locals,
                      ?_⟩
                    intro address _
                    exact congrFun hrel.2.2 address
                  exact ⟨0, hstate, hexception'⟩

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
    exact restoredCrepLocals_updateCrepLocalList state.locals temporaries values
      htemporaryLength htemporaryDistinct (by
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

theorem compile_full_pan_value_raise_state_relation_of_evidence_fuel
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
    (sourceFuel extraFuel : Nat) (exception : ExceptionId)
    (exceptionCode : α) (expression : Exp α) (sourceValue : PanValue α)
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
      (values.length + (freshNames context compiled.length 1).length + 2 + extraFuel)
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
  have hbase := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel hlookup hrel
    hsource hvalid hcompile hlength hcompiled hnot hfresh hexception
  have htarget := evalCrepFullProgState_raise_of_evidence_of_fuel
    context functions state crepPrimitive ffi sharedMem baseAddress topAddress
    exception exceptionCode expression compiled shape values extraFuel hlookup
    hcompile hlength hcompiled hnot hfresh
  exact ⟨hbase.1, htarget, hbase.2.2⟩

/-! Stateful Raise constructor for an arbitrary record of scalar source-word
    expressions.  The bounded-slot premise is the compiler-context invariant
    needed to keep the freshly allocated temporary names disjoint from every
    compiled field expression. -/
set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramStateCorrect_raise_source_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (fields : List (SourceWordExp α))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hbounded : ∀ (context : CompileContext α) (name : VarName)
      (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      ∀ slot ∈ slots, slot ≤ context.maxVar)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α)
      (name : Nat), name ∈ freshNames context fields.length 1 →
      state.locals name = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α) (values : List α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct (values.map PanValue.word)) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct (fields.map SourceWordExp.toExp))) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord
          (.rStruct (fields.map SourceWordExp.toExp)) with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some sourceValue =>
          cases sourceValue with
          | word value =>
              simp [evalPanValueExp] at hvalue
          | nStruct name values =>
              simp [evalPanValueExp] at hvalue
          | rStruct fieldValues =>
              have hsourceFields :
                  evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                    sourceMemory baseAddress topAddress bytesInWord
                    (fields.map SourceWordExp.toExp) = some fieldValues := by
                simpa [evalPanValueExp] using hvalue
              obtain ⟨values, hfields, hfieldsLength⟩ :=
                evalSourceWordExpList_inv structs sourceLocals sourceGlobals
                  sourceMemory baseAddress topAddress bytesInWord context state.locals
                  hrel.2.1
                  (fun name value hvalue =>
                    hlookup context sourceLocals name value hvalue)
                  fields fieldValues hsourceFields
              have hsourceFieldsValues :
                  evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                    sourceMemory baseAddress topAddress bytesInWord
                    (fields.map SourceWordExp.toExp) =
                    some (values.map (fun value => .word value)) := by
                simpa [hfields] using hsourceFields
              have hsourceValue :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord
                    (.rStruct (fields.map SourceWordExp.toExp)) =
                    some (.rStruct (values.map PanValue.word)) := by
                rw [hvalue, hfields]
              obtain ⟨compiled, hcompile, hcompiled⟩ :=
                compileSourceWordExp_rStruct_list_state_relation context structs
                  sourceLocals sourceGlobals sourceMemory state
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun name value hvalue =>
                    hlookup context sourceLocals name value hvalue)
                  fields values hsourceFieldsValues
              have hvaluesLength : compiled.length = values.length :=
                evalCrepFullExpsState_length state baseAddress topAddress
                  compiled values hcompiled
              have hshapeSize : ∀ (start : Nat) (entries : List α),
                  List.foldl (fun total field => total + field.shapeSize) start
                    (entries.map (fun _ => Shape.one)) = start + entries.length := by
                intro start entries
                induction entries generalizing start with
                | nil => simp
                | cons entry entries ih =>
                    simp [ih] <;> omega
              have hlength : compiled.length =
                  Shape.shapeSize (.comb (values.map (fun _ => Shape.one))) := by
                rw [hvaluesLength]
                simp [Shape.shapeSize, hshapeSize]
              have hslotBound : ∀ name shape slots,
                  lookupInfo name context.vars = some (shape, slots) →
                  ∀ slot ∈ slots, slot ≤ context.maxVar := by
                intro name shape slots hlookupName
                exact hbounded context name shape slots hlookupName
              have hcompiledBounded :
                  ∀ expression ∈ compiled, ∀ varName ∈ crepExpVars expression,
                    varName ≤ context.maxVar := by
                have hboundAll := compileExp_vars_bounded context hslotBound
                  (.rStruct (fields.map SourceWordExp.toExp))
                rw [hcompile] at hboundAll
                intro expression hexpression varName hvar
                apply hboundAll varName
                exact List.mem_flatMap.2 ⟨expression, hexpression, hvar⟩
              have hnot := freshNames_not_mem_of_expVars_bounded
                context compiled.length 1 compiled (by omega) hcompiledBounded
              have hcompiledFieldsLength : compiled.length = fields.length :=
                hvaluesLength.trans hfieldsLength
              have hfresh' : ∀ name ∈ freshNames context compiled.length 1,
                  state.locals name = none := by
                intro name hname
                apply hfresh context state name
                simpa [hcompiledFieldsLength] using hname
              obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
              have hvalid :
                  panValuePayloadWithinLimit structs
                    (.rStruct (values.map PanValue.word)) = true := by
                have hsource' := hsource
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue]
                  at hsource'
                exact hsource'.1
              have hsourceEq : sourceResult =
                  .raised (fun _ => none) sourceGlobals sourceMemory exception
                    (.rStruct (values.map PanValue.word)) := by
                have hsource' := hsource
                simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue, hvalid]
                  at hsource'
                exact hsource'.symm
              let temporaries := freshNames context compiled.length 1
              let body := crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  (temporaries.map (fun name => .var name)))
              have htemporaryLength : temporaries.length = values.length := by
                simp [temporaries, freshNames, hvaluesLength]
              have htemporaryDistinct : CrepDistinctNames temporaries := by
                exact crepDistinctNames_freshNames context
                  compiled.length 1
              have htemporaryCompiledLength : temporaries.length = compiled.length := by
                simp [temporaries, freshNames]
              have hcompileProg :
                  compileProg context
                      (.raise exception
                        (.rStruct (fields.map SourceWordExp.toExp))) =
                    .seq (nestedDecs temporaries compiled body)
                      (.raise exceptionCode) := by
                simp only [compileProg, hlookupCode, hcompile, hlength,
                  temporaries, body]
                rfl
              have hcrepSeq := hcrep
              rw [hcompileProg] at hcrepSeq
              cases targetFuel with
              | zero =>
                  simp [evalCrepFullProgState] at hcrepSeq
              | succ targetFuel =>
                  cases hfirst : evalCrepFullProgState functions crepPrimitive ffi
                      sharedMem baseAddress topAddress targetFuel state
                      (nestedDecs temporaries compiled body) with
                  | none =>
                      simp [evalCrepFullProgState, hfirst] at hcrepSeq
                  | some firstResult =>
                      obtain ⟨bodyFuel, bodyResult, hbodyFuel, hnested, hrestore⟩ :=
                        crepNestedDecsStateEval_of_eval
                          functions crepPrimitive ffi sharedMem baseAddress topAddress
                          targetFuel state temporaries compiled body firstResult
                          htemporaryDistinct htemporaryCompiledLength hfirst
                      have hbodyEval := crepNestedDecsStateEval_body_of_evalExps_stable
                        functions crepPrimitive ffi sharedMem baseAddress topAddress
                        bodyFuel state temporaries compiled body bodyResult values
                        htemporaryCompiledLength hnot hcompiled hnested
                      have hbodyValues := evalCrepFullExpsState_varList_updateCrepLocalList
                        state baseAddress topAddress temporaries values htemporaryLength
                        htemporaryDistinct
                      have hbodyFuelLower :=
                        evalCrepFullProgState_storeGlobals_vars_fuel_lower_bound
                          functions crepPrimitive ffi sharedMem baseAddress topAddress
                          bodyFuel
                          { state with locals :=
                              updateCrepLocalList state.locals temporaries values }
                          0 context.bytesInWord temporaries values bodyResult
                          (by simpa using htemporaryLength) hbodyValues hbodyEval
                      have hbaseFuel :
                          values.length + temporaries.length + 2 ≤ targetFuel + 1 := by
                        omega
                      obtain ⟨extraFuel, htargetFuel⟩ :=
                        Nat.exists_eq_add_of_le hbaseFuel
                      have hexception' :=
                        hexception context exceptionRel exceptionCode values hlookupCode
                      have hresult :=
                        compile_full_pan_value_raise_state_relation_of_evidence_fuel
                          context structs sourceFunctions functions sourceLocals sourceGlobals
                          sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                          baseAddress topAddress bytesInWord sourceFuel extraFuel exception
                          exceptionCode (.rStruct (fields.map SourceWordExp.toExp))
                          (.rStruct (values.map PanValue.word)) compiled
                          (.comb (values.map (fun _ => Shape.one))) values exceptionRel
                          hlookupCode (hrel := hrel) hsourceValue hvalid hcompile hlength
                          hcompiled hnot hfresh' hexception'
                      have hsourceEq' := Option.some.inj (hresult.1.symm.trans hsource)
                      have hcrepAligned :
                          evalCrepFullProgState functions crepPrimitive ffi sharedMem
                            baseAddress topAddress
                            (values.length + temporaries.length + 2 + extraFuel)
                            state
                            (compileProg context
                              (.raise exception
                                (.rStruct (fields.map SourceWordExp.toExp)))) =
                          some crepResult := by
                        simpa [hcompileProg, htargetFuel] using hcrepSeq
                      have hcrepEq :=
                        Option.some.inj (hresult.2.1.symm.trans hcrepAligned)
                      cases hsourceEq'
                      cases hcrepEq
                      exact ⟨0, hresult.2.2⟩

theorem panValueCrepProgramStateCorrect_raise_one_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (value : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct [.word value]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct [.const value])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord (.rStruct [.const value]) =
            some (.rStruct [.word value]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context (.rStruct [.const value]) =
            ([.const value], .comb [.one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs (.rStruct [.word value]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress [.const value] =
            some [value] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength : [(.const value : CrepExp α)].length =
          Shape.shapeSize (.comb [.one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 1 1,
          ∀ expression ∈ ([.const value] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh : ∀ name ∈ freshNames context 1 1,
          state.locals name = none := by
        simpa [freshNames] using hfresh context state
      have hexception' := hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 1 1 =
          [context.maxVar + 1] := by
        simp [freshNames, List.range, List.range.loop]
      have hcompileProg : compileProg context
          (.raise exception (.rStruct [.const value])) =
          .seq
            (nestedDecs [context.maxVar + 1] [.const value]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      rw [hcompileProg] at hcrep
                      have hfreshName : state.locals (context.maxVar + 1) = none := by
                        exact hfresh (context.maxVar + 1) (by
                          rw [hnames]
                          simp)
                      simp [evalCrepFullProgState, evalCrepFullExpState,
                        nestedDecs, crepNestedSeq, storeGlobals, hfreshName,
                        updateCrepLocal, restoreCrepResult] at hcrep
                      have hrestore :
                          restoreCrepLocal
                              (updateCrepLocal state.locals
                                (context.maxVar + 1) value)
                              (context.maxVar + 1) none = state.locals := by
                        funext current
                        by_cases hcurrent : current = context.maxVar + 1
                        · subst current
                          simp [restoreCrepLocal, hfreshName]
                        · simp [restoreCrepLocal, updateCrepLocal, hcurrent]
                      rw [hrestore] at hcrep
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                        hsourceValue, panValuePayloadWithinLimit] at hsource
                      have hsourceEq := hsource.2
                      have hcrepEq := hcrep
                      cases hsourceEq
                      cases hcrepEq
                      have hstate : panValueCrepRaisedStateRel structs context
                          sourceGlobals sourceMemory
                          { state with
                              globals := updateMemory state.globals 0 value } 0 := by
                        refine ⟨hrel.1,
                          panValueCrepLocalsRel_empty structs context state.locals,
                          ?_⟩
                        intro address _
                        exact congrFun hrel.2.2 address
                      exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_nested_one_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (value : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct [.rStruct [.word value]]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct [.rStruct [.const value]])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.rStruct [.const value]]) =
          some (.rStruct [.rStruct [.word value]]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context (.rStruct [.rStruct [.const value]]) =
            ([.const value], .comb [.comb [.one]]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.rStruct [.word value]]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress [.const value] =
            some [value] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength : [(.const value : CrepExp α)].length =
          Shape.shapeSize (.comb [.comb [.one]]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 1 1,
          ∀ expression ∈ ([.const value] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh : ∀ name ∈ freshNames context 1 1,
          state.locals name = none := by
        simpa [freshNames] using hfresh context state
      have hexception' := hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 1 1 = [context.maxVar + 1] := by
        simp [freshNames, List.range, List.range.loop]
      have hcompileProg : compileProg context
          (.raise exception (.rStruct [.rStruct [.const value]])) =
          .seq
            (nestedDecs [context.maxVar + 1] [.const value]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      rw [hcompileProg] at hcrep
                      have hfreshName : state.locals (context.maxVar + 1) = none := by
                        exact hfresh (context.maxVar + 1) (by
                          rw [hnames]
                          simp)
                      simp [evalCrepFullProgState, evalCrepFullExpState,
                        nestedDecs, crepNestedSeq, storeGlobals, hfreshName,
                        updateCrepLocal, restoreCrepResult] at hcrep
                      have hrestore :
                          restoreCrepLocal
                              (updateCrepLocal state.locals
                                (context.maxVar + 1) value)
                              (context.maxVar + 1) none = state.locals := by
                        funext current
                        by_cases hcurrent : current = context.maxVar + 1
                        · subst current
                          simp [restoreCrepLocal, hfreshName]
                        · simp [restoreCrepLocal, updateCrepLocal, hcurrent]
                      rw [hrestore] at hcrep
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                        hsourceValue, panValuePayloadWithinLimit] at hsource
                      have hsourceEq := hsource.2
                      have hcrepEq := hcrep
                      cases hsourceEq
                      cases hcrepEq
                      have hstate : panValueCrepRaisedStateRel structs context
                          sourceGlobals sourceMemory
                          { state with
                              globals := updateMemory state.globals 0 value } 0 := by
                        refine ⟨hrel.1,
                          panValueCrepLocalsRel_empty structs context state.locals,
                          ?_⟩
                        intro address _
                        exact congrFun hrel.2.2 address
                      exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_two_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (left right : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.rStruct [.word left, .word right]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception (.rStruct [.const left, .const right])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const left, .const right]) =
            some (.rStruct [.word left, .word right]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context (.rStruct [.const left, .const right]) =
            ([.const left, .const right], .comb [.one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word left, .word right]) = true := by
        exact panValuePayloadWithinLimit_rStruct_two_words structs left right
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const left, .const right] = some [left, right] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const left : CrepExp α), .const right].length =
            Shape.shapeSize (.comb [.one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 2 1,
          ∀ expression ∈ ([.const left, .const right] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 2 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1 (hfresh context state).2
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 2 1 =
          [context.maxVar + 1, context.maxVar + 2] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception (.rStruct [.const left, .const right])) =
          .seq
            (nestedDecs [context.maxVar + 1, context.maxVar + 2]
              [.const left, .const right]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState, evalCrepFullExpState,
                                updateCrepLocal, restoreCrepResult] at hcrep
                          | succ targetFuel =>
                              rw [hcompileProg] at hcrep
                              have hfreshLeft :
                                  state.locals (context.maxVar + 1) = none := by
                                exact (hfresh context state).1
                              have hfreshRight :
                                  state.locals (context.maxVar + 2) = none := by
                                exact (hfresh context state).2
                              simp [evalCrepFullProgState, evalCrepFullExpState,
                                nestedDecs, crepNestedSeq, storeGlobals,
                                hfreshLeft, hfreshRight, updateCrepLocal,
                                restoreCrepResult] at hcrep
                              have hrestore :
                                  restoreCrepLocal
                                      (restoreCrepLocal
                                        (updateCrepLocal
                                          (updateCrepLocal state.locals
                                            (context.maxVar + 1) left)
                                          (context.maxVar + 2) right)
                                        (context.maxVar + 2) none)
                                      (context.maxVar + 1) none = state.locals := by
                                funext current
                                by_cases hcurrentRight : current = context.maxVar + 2
                                · subst current
                                  simp [restoreCrepLocal, hfreshRight]
                                · by_cases hcurrentLeft : current = context.maxVar + 1 <;>
                                    simp [restoreCrepLocal, updateCrepLocal,
                                      hcurrentRight, hcurrentLeft, hfreshLeft]
                              rw [hrestore] at hcrep
                              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                hsourceValue, panValuePayloadWithinLimit] at hsource
                              have hsourceEq := hsource.2
                              have hcrepEq := hcrep
                              cases hsourceEq
                              cases hcrepEq
                              have hstate : panValueCrepRaisedStateRel structs context
                                  sourceGlobals sourceMemory
                                  { state with
                                      globals :=
                                        updateMemory
                                          (updateMemory state.globals 0 left)
                                          (0 + bytesInWord) right } 0 := by
                                refine ⟨hrel.1,
                                  panValueCrepLocalsRel_empty structs context state.locals,
                                  ?_⟩
                                intro address _
                                exact congrFun hrel.2.2 address
                              exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_three_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (first second third : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none ∧
      state.locals (context.maxVar + 3) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception
        (.rStruct [.word first, .word second, .word third]) exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception
        (.rStruct [.const first, .const second, .const third])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const first, .const second, .const third]) =
            some (.rStruct [.word first, .word second, .word third]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context
              (.rStruct [.const first, .const second, .const third]) =
            ([.const first, .const second, .const third],
              .comb [.one, .one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word first, .word second, .word third]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const first, .const second, .const third] =
              some [first, second, third] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const first : CrepExp α), .const second, .const third].length =
            Shape.shapeSize (.comb [.one, .one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 3 1,
          ∀ expression ∈
            ([.const first, .const second, .const third] : List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 3 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1
            (And.intro (hfresh context state).2.1 (hfresh context state).2.2)
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 3 1 =
          [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception
            (.rStruct [.const first, .const second, .const third])) =
          .seq
            (nestedDecs
              [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3]
              [.const first, .const second, .const third]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2),
                    .var (context.maxVar + 3)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState] at hcrep
                          | succ targetFuel =>
                              cases targetFuel with
                              | zero =>
                                  rw [hcompileProg] at hcrep
                                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                                    evalCrepFullProgState, evalCrepFullExpState,
                                    updateCrepLocal, restoreCrepResult] at hcrep
                              | succ targetFuel =>
                                  cases targetFuel with
                                  | zero =>
                                      rw [hcompileProg] at hcrep
                                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                                        evalCrepFullProgState, evalCrepFullExpState,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                  | succ targetFuel =>
                                      rw [hcompileProg] at hcrep
                                      have hfreshFirst :
                                          state.locals (context.maxVar + 1) = none := by
                                        exact (hfresh context state).1
                                      have hfreshSecond :
                                          state.locals (context.maxVar + 2) = none := by
                                        exact (hfresh context state).2.1
                                      have hfreshThird :
                                          state.locals (context.maxVar + 3) = none := by
                                        exact (hfresh context state).2.2
                                      simp [evalCrepFullProgState,
                                        evalCrepFullExpState, nestedDecs,
                                        crepNestedSeq, storeGlobals,
                                        hfreshFirst, hfreshSecond, hfreshThird,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                      have hrestore :
                                          restoreCrepLocal
                                              (restoreCrepLocal
                                                (restoreCrepLocal
                                                  (updateCrepLocal
                                                    (updateCrepLocal
                                                      (updateCrepLocal state.locals
                                                        (context.maxVar + 1) first)
                                                      (context.maxVar + 2) second)
                                                    (context.maxVar + 3) third)
                                                  (context.maxVar + 3) none)
                                                (context.maxVar + 2) none)
                                              (context.maxVar + 1) none =
                                            state.locals := by
                                        funext current
                                        by_cases hcurrentThird :
                                            current = context.maxVar + 3
                                        · subst current
                                          simp [restoreCrepLocal, hfreshThird]
                                        · by_cases hcurrentSecond :
                                            current = context.maxVar + 2
                                          · subst current
                                            simp [restoreCrepLocal, hfreshSecond]
                                          · by_cases hcurrentFirst :
                                              current = context.maxVar + 1 <;>
                                              simp [restoreCrepLocal,
                                                updateCrepLocal, hcurrentThird,
                                                hcurrentSecond, hcurrentFirst,
                                                hfreshFirst]
                                      rw [hrestore] at hcrep
                                      simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                        hsourceValue, panValuePayloadWithinLimit] at hsource
                                      have hsourceEq := hsource.2
                                      have hcrepEq := hcrep
                                      cases hsourceEq
                                      cases hcrepEq
                                      have hstate :
                                          panValueCrepRaisedStateRel structs context
                                            sourceGlobals sourceMemory
                                            { state with
                                                globals :=
                                                  updateMemory
                                                    (updateMemory
                                                      (updateMemory state.globals 0 first)
                                                      (0 + bytesInWord) second)
                                                    ((0 + bytesInWord) + bytesInWord)
                                                      third } 0 := by
                                        refine ⟨hrel.1,
                                          panValueCrepLocalsRel_empty structs context
                                            state.locals, ?_⟩
                                        intro address _
                                        exact congrFun hrel.2.2 address
                                      exact ⟨0, hstate, hexception'⟩

theorem panValueCrepProgramStateCorrect_raise_four_word_record
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (first second third fourth : α)
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none ∧
      state.locals (context.maxVar + 2) = none ∧
      state.locals (context.maxVar + 3) = none ∧
      state.locals (context.maxVar + 4) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception
        (.rStruct [.word first, .word second, .word third, .word fourth])
        exceptionCode) :
    PanValueCrepProgramStateCorrect
      (.raise exception
        (.rStruct [.const first, .const second, .const third, .const fourth])) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      obtain ⟨exceptionCode, hlookupCode⟩ := hlookupException context
      have hsourceValue :
          evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord
            (.rStruct [.const first, .const second, .const third, .const fourth]) =
            some (.rStruct [.word first, .word second, .word third, .word fourth]) := by
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]
      have hcompile :
          compileExp context
              (.rStruct [.const first, .const second, .const third, .const fourth]) =
            ([.const first, .const second, .const third, .const fourth],
              .comb [.one, .one, .one, .one]) := by
        simp [compileExp, compileExp.compileExpList]
      have hvalid :
          panValuePayloadWithinLimit structs
            (.rStruct [.word first, .word second, .word third, .word fourth]) = true := by
        simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
          panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
          panValueFlatValueFuel,
          panValueFlatValueFuel.panValueFlatValueListFuel]
      have hcompiled :
          evalCrepFullExpsState state baseAddress topAddress
            [.const first, .const second, .const third, .const fourth] =
              some [first, second, third, fourth] := by
        simp [evalCrepFullExpsState, evalCrepFullExpState]
      have hlength :
          [(.const first : CrepExp α), .const second, .const third,
            .const fourth].length =
            Shape.shapeSize (.comb [.one, .one, .one, .one]) := by
        simp [Shape.shapeSize]
      have hnot : ∀ name ∈ freshNames context 4 1,
          ∀ expression ∈
            ([.const first, .const second, .const third, .const fourth] :
              List (CrepExp α)),
            name ∉ crepExpVars expression := by
        simp [freshNames]
      have hfresh' : ∀ name ∈ freshNames context 4 1,
          state.locals name = none := by
        simpa [freshNames, List.range, List.range.loop, Nat.add_assoc] using
          And.intro (hfresh context state).1
            (And.intro (hfresh context state).2.1
              (And.intro (hfresh context state).2.2.1 (hfresh context state).2.2.2))
      have hexception' :=
        hexception context exceptionRel exceptionCode hlookupCode
      have hnames : freshNames context 4 1 =
          [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3,
            context.maxVar + 4] := by
        simp [freshNames, List.range, List.range.loop, Nat.add_assoc]
      have hcompileProg : compileProg context
          (.raise exception
            (.rStruct [.const first, .const second, .const third, .const fourth])) =
          .seq
            (nestedDecs
              [context.maxVar + 1, context.maxVar + 2, context.maxVar + 3,
                context.maxVar + 4]
              [.const first, .const second, .const third, .const fourth]
              (crepNestedSeq
                (storeGlobals 0 context.bytesInWord
                  [.var (context.maxVar + 1), .var (context.maxVar + 2),
                    .var (context.maxVar + 3), .var (context.maxVar + 4)])))
            (.raise exceptionCode) := by
        simp [compileProg, hlookupCode, hcompile, hlength,
          freshNames, Shape.shapeSize, List.range, List.range.loop,
          nestedDecs, crepNestedSeq, storeGlobals]
      cases targetFuel with
      | zero =>
          rw [hcompileProg] at hcrep
          simp [nestedDecs, crepNestedSeq, storeGlobals,
            evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              rw [hcompileProg] at hcrep
              simp [nestedDecs, crepNestedSeq, storeGlobals,
                evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  rw [hcompileProg] at hcrep
                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                    evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      rw [hcompileProg] at hcrep
                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                        evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          rw [hcompileProg] at hcrep
                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                            evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          cases targetFuel with
                          | zero =>
                              rw [hcompileProg] at hcrep
                              simp [nestedDecs, crepNestedSeq, storeGlobals,
                                evalCrepFullProgState] at hcrep
                          | succ targetFuel =>
                              cases targetFuel with
                              | zero =>
                                  rw [hcompileProg] at hcrep
                                  simp [nestedDecs, crepNestedSeq, storeGlobals,
                                    evalCrepFullProgState] at hcrep
                              | succ targetFuel =>
                                  cases targetFuel with
                                  | zero =>
                                      rw [hcompileProg] at hcrep
                                      simp [nestedDecs, crepNestedSeq, storeGlobals,
                                        evalCrepFullProgState, evalCrepFullExpState,
                                        updateCrepLocal, restoreCrepResult] at hcrep
                                  | succ targetFuel =>
                                      cases targetFuel with
                                      | zero =>
                                          rw [hcompileProg] at hcrep
                                          simp [nestedDecs, crepNestedSeq, storeGlobals,
                                            evalCrepFullProgState, evalCrepFullExpState,
                                            updateCrepLocal, restoreCrepResult] at hcrep
                                      | succ targetFuel =>
                                          cases targetFuel with
                                          | zero =>
                                              rw [hcompileProg] at hcrep
                                              simp [nestedDecs, crepNestedSeq,
                                                storeGlobals, evalCrepFullProgState,
                                                evalCrepFullExpState,
                                                updateCrepLocal, restoreCrepResult] at hcrep
                                          | succ targetFuel =>
                                              rw [hcompileProg] at hcrep
                                              have hfreshFirst :
                                                  state.locals (context.maxVar + 1) = none := by
                                                exact (hfresh context state).1
                                              have hfreshSecond :
                                                  state.locals (context.maxVar + 2) = none := by
                                                exact (hfresh context state).2.1
                                              have hfreshThird :
                                                  state.locals (context.maxVar + 3) = none := by
                                                exact (hfresh context state).2.2.1
                                              have hfreshFourth :
                                                  state.locals (context.maxVar + 4) = none := by
                                                exact (hfresh context state).2.2.2
                                              simp [evalCrepFullProgState,
                                                evalCrepFullExpState, nestedDecs,
                                                crepNestedSeq, storeGlobals,
                                                hfreshFirst, hfreshSecond, hfreshThird,
                                                hfreshFourth, updateCrepLocal,
                                                restoreCrepResult] at hcrep
                                              have hrestore :
                                                  restoreCrepLocal
                                                      (restoreCrepLocal
                                                        (restoreCrepLocal
                                                          (restoreCrepLocal
                                                            (updateCrepLocal
                                                              (updateCrepLocal
                                                                (updateCrepLocal
                                                                  (updateCrepLocal state.locals
                                                                    (context.maxVar + 1) first)
                                                                  (context.maxVar + 2) second)
                                                                (context.maxVar + 3) third)
                                                              (context.maxVar + 4) fourth)
                                                            (context.maxVar + 4) none)
                                                          (context.maxVar + 3) none)
                                                        (context.maxVar + 2) none)
                                                      (context.maxVar + 1) none =
                                                    state.locals := by
                                                funext current
                                                by_cases hcurrentFourth :
                                                    current = context.maxVar + 4
                                                · subst current
                                                  simp [restoreCrepLocal, hfreshFourth]
                                                · by_cases hcurrentThird :
                                                    current = context.maxVar + 3
                                                  · subst current
                                                    simp [restoreCrepLocal, hfreshThird]
                                                  · by_cases hcurrentSecond :
                                                      current = context.maxVar + 2
                                                    · subst current
                                                      simp [restoreCrepLocal, hfreshSecond]
                                                    · by_cases hcurrentFirst :
                                                        current = context.maxVar + 1 <;>
                                                        simp [restoreCrepLocal,
                                                          updateCrepLocal,
                                                          hcurrentFourth,
                                                          hcurrentThird,
                                                          hcurrentSecond,
                                                          hcurrentFirst,
                                                          hfreshFirst]
                                              rw [hrestore] at hcrep
                                              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                                                hsourceValue, panValuePayloadWithinLimit] at hsource
                                              have hsourceEq := hsource.2
                                              have hcrepEq := hcrep
                                              cases hsourceEq
                                              cases hcrepEq
                                              have hstate :
                                                  panValueCrepRaisedStateRel structs context
                                                    sourceGlobals sourceMemory
                                                    { state with
                                                        globals :=
                                                          updateMemory
                                                            (updateMemory
                                                              (updateMemory
                                                                (updateMemory state.globals 0 first)
                                                                (0 + bytesInWord) second)
                                                              ((0 + bytesInWord) + bytesInWord)
                                                                third)
                                                            (((0 + bytesInWord) + bytesInWord) +
                                                              bytesInWord) fourth } 0 := by
                                                refine ⟨hrel.1,
                                                  panValueCrepLocalsRel_empty structs context
                                                    state.locals, ?_⟩
                                                intro address _
                                                exact congrFun hrel.2.2 address
                                              exact ⟨0, hstate, hexception'⟩

end Flapjack
