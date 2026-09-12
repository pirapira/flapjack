import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeCompileExpVariables
import Flapjack.CrepeProgramGenericAssignmentConstructor
import Flapjack.CrepeProgramGenericAssignmentTemporaryConstructor
import Flapjack.CrepeProgramAssignmentFuelRelation
import Flapjack.PanValueShapeInversion

/-!
The assignment proof dispatcher.  The compiler chooses direct or
fresh-temporary lowering from `distinctLists`; this theorem packages that
choice so the syntax-induction assignment case only supplies expression and
static-context contracts.
-/

namespace Flapjack

theorem evalCrepFullExps_length
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) (expressions : List (CrepExp α))
    (values : List α)
    (h : evalCrepFullExps locals memory baseAddress topAddress expressions =
      some values) :
    expressions.length = values.length := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp [evalCrepFullExps] at h
  | cons expression expressions ih =>
      cases values with
      | nil =>
          cases hhead : evalCrepFullExp locals memory baseAddress topAddress expression with
          | none => simp [evalCrepFullExps, hhead] at h
          | some headValue =>
              cases htail : evalCrepFullExps locals memory baseAddress topAddress expressions with
              | none => simp [evalCrepFullExps, hhead, htail] at h
              | some tailValues =>
                  simp [evalCrepFullExps, hhead, htail] at h
      | cons value values =>
          cases hhead : evalCrepFullExp locals memory baseAddress topAddress expression with
          | none =>
              simp [evalCrepFullExps, hhead] at h
          | some headValue =>
              cases htail : evalCrepFullExps locals memory baseAddress topAddress expressions with
              | none =>
                  simp [evalCrepFullExps, hhead, htail] at h
              | some tailValues =>
                  have htailLength := ih tailValues htail
                  have hvalues : headValue :: tailValues = value :: values := by
                    simpa [evalCrepFullExps, hhead, htail] using h
                  cases hvalues
                  simp [htailLength]

theorem panValueCrepProgramCorrect_assign_local_of_expression_contract
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : Exp α)
    (hvalue : PanValueCrepExpressionCorrect expression)
    (hdirect : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)) (compileShape shape : Shape)
      (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      distinctLists slots (compiled.flatMap crepExpVars) = true)
    (hmetadata : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceValue : PanValue α)
      (compileShape shape : Shape) (slots : List Nat) (values : List α),
      lookupInfo name context.vars = some (shape, slots) →
      compileShape = panValueShape structs sourceValue →
      panShapeMatches (panValueShape structs sourceValue) shape = true →
      slots.length = values.length ∧ CrepDistinctNames slots)
    (htemporaryPath : ∀ (context : CompileContext α) (structs : StructContext)
      (_sourceValue : PanValue α) (_values : List α) (compiled : List (CrepExp α))
      (compileShape shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      compileShape = panValueShape structs _sourceValue →
      panShapeMatches (panValueShape structs _sourceValue) shape = true →
      distinctLists slots (compiled.flatMap crepExpVars) = false)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α)) (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ shape slots, lookupInfo name context.vars = some (shape, slots))
    (hbounded : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ oldSlots, slot ≤ context.maxVar)
    (hnoalias : ∀ (context : CompileContext α) (shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        ∀ slot ∈ slots, slot ∉ oldSlots) :
    PanValueCrepProgramCorrect (.assign .local name expression) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs sourceValue)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name sourceValue)
        sourceGlobals sourceMemory := by
    cases sourceFuel with
    | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name expression) = some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue', hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name expression sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue', hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hsourceValue, hold, hvalid, hsourceResult⟩ := hsourceInfo
  have hcontract : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some sourceValue →
      ∃ compiled compileShape values,
        compileExp context expression = (compiled, compileShape) ∧
        compileShape = panValueShape structs sourceValue ∧
        compiled.length = values.length ∧
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiled = some values ∧
        panValueFlatWords sourceValue = values := by
    intro context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hsource
    obtain ⟨hlimit, compiled, hcompile, hcompiled⟩ :=
      hvalue context structs sourceLocals sourceGlobals sourceMemory state
        baseAddress topAddress bytesInWord sourceValue hrel hsource
    let values := panValueFlatWords sourceValue
    refine ⟨compiled, panValueShape structs sourceValue, values, hcompile, rfl, ?_, ?_, rfl⟩
    · exact evalCrepFullExps_length state.locals state.memory baseAddress topAddress
        compiled values (by simpa [values] using hcompiled)
    · simpa [values] using hcompiled
  obtain ⟨compiled, compileShape, values, hcompile, hcompileShape,
      hcompiledLength, hcompiled, hflat⟩ :=
    hcontract context structs sourceLocals sourceGlobals sourceMemory state
      baseAddress topAddress bytesInWord sourceValue hrel hsourceValue
  obtain ⟨shape, slots, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue shape slots hold hlookupName
  have hshapeNewContext : panShapeMatches
      (panValueShape structs sourceValue) shape = true := by
    exact panShapeMatches_trans
      (panValueShape structs sourceValue) (panValueShape structs oldValue) shape
      hvalid holdRel.1
  have htemporaryPath' : ∀ (context : CompileContext α) (structs : StructContext)
      (_sourceValue : PanValue α) (_values : List α) (compiled : List (CrepExp α))
      (compileShape shape : Shape) (slots : List Nat),
      lookupInfo name context.vars = some (shape, slots) →
      compileExp context expression = (compiled, compileShape) →
      compileShape = panValueShape structs _sourceValue →
      panShapeMatches (panValueShape structs _sourceValue) shape = true →
      distinctLists slots (compiled.flatMap crepExpVars) = false ∧
      (∀ expression ∈ compiled, ∀ varName ∈ crepExpVars expression,
        varName ≤ context.maxVar) := by
    intro context structs sourceValue values compiled compileShape shape slots
      hlookupName hcompile hcompileShape hshape
    constructor
    · exact htemporaryPath context structs sourceValue values compiled compileShape
        shape slots hlookupName hcompile hcompileShape hshape
    · intro compiledExpression hcompiledExpression varName hvar
      have hslotBound : ∀ oldName oldShape oldSlots,
          lookupInfo oldName context.vars = some (oldShape, oldSlots) →
          ∀ slot ∈ oldSlots, slot ≤ context.maxVar := by
        intro oldName oldShape oldSlots hlookupOld
        exact hbounded context oldName oldShape oldSlots hlookupOld
      have hboundAll := compileExp_vars_bounded context hslotBound expression
      rw [hcompile] at hboundAll
      apply hboundAll
      exact List.mem_flatMap.2 ⟨compiledExpression, hcompiledExpression, hvar⟩
  by_cases hdirectMode : distinctLists slots (compiled.flatMap crepExpVars) = true
  · exact panValueCrepProgramCorrect_assign_local_direct name expression hcontract
      hdirect hmetadata hlookup hnoalias context structs sourceFunctions functions
      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler crepPrimitive
      ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
      sourceResult crepResult hrel hsource hcrep
  · exact panValueCrepProgramCorrect_assign_local_temporary name expression hcontract
      htemporaryPath' hmetadata hbounded hlookup hnoalias context structs sourceFunctions functions
      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler crepPrimitive
      ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
      sourceResult crepResult hrel hsource hcrep

theorem panValueCrepProgramStateCorrect_assign_local_source_word_direct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : SourceWordExp α)
    (hdirect : ∀ (context : CompileContext α) (compiled : CrepExp α)
      (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      compileExp context expression.toExp = ([compiled], .one) →
      distinctLists [slot] (crepExpVars compiled) = true)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupAll : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (localName : VarName) (localValue : PanValue α),
      sourceLocals localName = some localValue →
      ∃ slot, lookupInfo localName context.vars = some (.one, [slot]))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hnoalias : ∀ (context : CompileContext α)
      (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        slot ∉ oldSlots) :
    PanValueCrepProgramStateCorrect
      (.assign .local name expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression.toExp = some sourceValue ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs sourceValue)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name sourceValue)
        sourceGlobals sourceMemory := by
    cases sourceFuel with
    | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name expression.toExp) = some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name expression.toExp sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hsourceValue, hold, hvalid, hsourceResult⟩ := hsourceInfo
  obtain ⟨slot, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue .one [slot] hold hlookupName
  obtain ⟨oldWord, holdWord⟩ := panValueShape_matches_one_inv structs oldValue holdRel.1
  obtain ⟨value, hsourceWord⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord context hrel.2.1
    (hlookupAll context sourceLocals) expression sourceValue hsourceValue
  subst sourceValue
  subst oldValue
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord (hbytesInWord context bytesInWord)
    hrel.2.1 (hlookupAll context sourceLocals) expression value hsourceValue
  have hcompile' : compileExp context expression.toExp = ([compiled], .one) := by
    simpa using hcompile
  have hdistinct := hdirect context compiled slot hlookupName hcompile'
  have hcompileProg : compileProg context
      (.assign .local name expression.toExp) =
      .seq (.assign slot compiled) .skip := by
    simp [compileProg, hlookupName, hcompile', hdistinct, crepNestedSeq]
  rw [hcompileProg] at hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero => simp [evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              have hcrepOriginal :
                  evalCrepFullProgState functions crepPrimitive ffi sharedMem
                    baseAddress topAddress (targetFuel + 2) state
                    (compileProg context (.assign .local name expression.toExp)) =
                    some crepResult := by
                simpa [hcompileProg] using hcrep
              obtain ⟨hsourceExpected, hcrepExpected, hrelation⟩ :=
                compile_full_pan_value_local_assign_source_word_state_relation_fuel
                  context structs sourceFunctions functions sourceLocals sourceGlobals
                  sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                  baseAddress topAddress bytesInWord sourceFuel targetFuel name slot
                  oldWord value expression compiled hlookupName
                  (hlookupAll context sourceLocals) hold hsourceValue hcompile'
                  hcompiled hdistinct hrel
                  (hnoalias context slot hlookupName)
              have hsourceEq := Option.some.inj (hsourceExpected.symm.trans hsource)
              have hcrepEq := Option.some.inj
                (hcrepExpected.symm.trans hcrepOriginal)
              cases hsourceEq
              cases hcrepEq
              exact hrelation

theorem panValueCrepProgramStateCorrect_assign_local_source_word_temporary
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : SourceWordExp α)
    (htemporaryPath : ∀ (context : CompileContext α) (compiled : CrepExp α)
      (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      compileExp context expression.toExp = ([compiled], .one) →
      distinctLists [slot] (crepExpVars compiled) = false)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupAll : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (localName : VarName) (localValue : PanValue α),
      sourceLocals localName = some localValue →
      ∃ slot, lookupInfo localName context.vars = some (.one, [slot]))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hfreshNe : ∀ (context : CompileContext α) (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      context.maxVar + 1 ≠ slot)
    (hnoalias : ∀ (context : CompileContext α)
      (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        slot ∉ oldSlots) :
    PanValueCrepProgramStateCorrect
      (.assign .local name expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hsourceInfo : ∃ sourceValue oldValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression.toExp = some sourceValue ∧
      sourceLocals name = some oldValue ∧
      panShapeMatches (panValueShape structs sourceValue)
        (panValueShape structs oldValue) = true ∧
      sourceResult = .normal (updatePanValueMap sourceLocals name sourceValue)
        sourceGlobals sourceMemory := by
    cases sourceFuel with
    | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
    | succ sourceFuel =>
        have hsource' : evalPanValueProgWithPrimitiveCallsAndFfi
            primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord (sourceFuel + 1)
            sourceLocals sourceGlobals sourceMemory
            (.assign .local name expression.toExp) = some sourceResult := by
          simpa using hsource
        obtain ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩ :=
          evalPanValueProg_assign_local_inv primitive sourceHandler structs sourceFunctions
            baseAddress topAddress bytesInWord sourceFuel sourceLocals sourceGlobals
            sourceMemory name expression.toExp sourceResult hsource'
        exact ⟨sourceValue, oldValue, hvalue, hold, hvalid, hresult⟩
  obtain ⟨sourceValue, oldValue, hsourceValue, hold, _, hsourceResult⟩ := hsourceInfo
  obtain ⟨slot, hlookupName⟩ := hlookup context sourceLocals oldValue hold
  have holdRel := hrel.2.1 name oldValue .one [slot] hold hlookupName
  obtain ⟨oldWord, holdWord⟩ := panValueShape_matches_one_inv structs oldValue holdRel.1
  obtain ⟨value, hsourceWord⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord context hrel.2.1
    (hlookupAll context sourceLocals) expression sourceValue hsourceValue
  subst sourceValue
  subst oldValue
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord (hbytesInWord context bytesInWord)
    hrel.2.1 (hlookupAll context sourceLocals) expression value hsourceValue
  have hcompile' : compileExp context expression.toExp = ([compiled], .one) := by
    simpa using hcompile
  have hnotDistinct := htemporaryPath context compiled slot hlookupName hcompile'
  have hcompileProg : compileProg context
      (.assign .local name expression.toExp) =
      .dec (context.maxVar + 1) compiled
        (.seq (.assign slot (.var (context.maxVar + 1))) .skip) := by
    simp [compileProg, hlookupName, hcompile', hnotDistinct, freshNames,
      nestedDecs, crepNestedSeq]
  rw [hcompileProg] at hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases targetFuel with
          | zero => simp [evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              cases targetFuel with
              | zero => simp [evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  have hcrepOriginal :
                      evalCrepFullProgState functions crepPrimitive ffi sharedMem
                        baseAddress topAddress (targetFuel + 3) state
                        (compileProg context (.assign .local name expression.toExp)) =
                        some crepResult := by
                    simpa [hcompileProg] using hcrep
                  obtain ⟨hsourceExpected, hcrepExpected, hrelation⟩ :=
                    compile_full_pan_value_local_assign_source_word_temporary_state_relation_fuel
                      context structs sourceFunctions functions sourceLocals sourceGlobals
                      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                      baseAddress topAddress bytesInWord sourceFuel targetFuel name slot
                      (context.maxVar + 1) oldWord value expression compiled hlookupName
                      (hlookupAll context sourceLocals) hold hsourceValue hcompile' hcompiled
                      hnotDistinct rfl
                      (hfresh context state)
                      (hfreshNe context slot hlookupName) hrel
                      (hnoalias context slot hlookupName)
                  have hsourceEq := Option.some.inj
                    (hsourceExpected.symm.trans hsource)
                  have hcrepEq := Option.some.inj
                    (hcrepExpected.symm.trans hcrepOriginal)
                  cases hsourceEq
                  cases hcrepEq
                  exact hrelation

end Flapjack
