import Flapjack.CrepeNestedDecsStability
import Flapjack.CrepeDeclarationFuelInversion
import Flapjack.CrepeProgramDeclarationRestoration
import Flapjack.CrepeExpressionListRelation
import Flapjack.CrepeStateRelationExtension
import Flapjack.CrepeProgramRelation
import Flapjack.CrepeSourceWordRecordCorrectness

/-!
Compositional correctness for a declaration binding an arbitrary record of
scalar word expressions.  The source record, Crep temporary list, shape, and
restoration all scale with the field list.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_dec_word_record_general
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (fields : List (SourceWordExp α)) (body : Prog α)
    (hbody : PanValueCrepProgramCorrect body)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hname : ∀ (context : CompileContext α),
      lookupInfo name context.vars = none)
    (hfresh : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈
        allocatedNames context (.comb (fields.map (fun _ => .one))) →
        temporary ∉ oldSlots)
    (hcompiledFresh : ∀ (context : CompileContext α)
      (compiled : List (CrepExp α)),
      compileExp.compileExpList context
        (fields.map SourceWordExp.toExp) =
        compiled.map (fun compiled => ([compiled], .one)) →
      ∀ temporary, temporary ∈
        allocatedNames context (.comb (fields.map (fun _ => .one))) →
      ∀ expression ∈ compiled, temporary ∉ crepExpVars expression) :
    PanValueCrepProgramCorrect
      (.dec name (.comb (fields.map (fun _ => .one)))
        (.rStruct (fields.map SourceWordExp.toExp)) body) := by
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
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            hvalue] at hsource
      | some sourceValue =>
          have hsourceDecomp : ∃ fieldValues,
              evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                sourceMemory baseAddress topAddress bytesInWord
                (fields.map SourceWordExp.toExp) = some fieldValues ∧
              .rStruct fieldValues = sourceValue := by
            simpa [evalPanValueExp] using hvalue
          obtain ⟨fieldValues, hfields, hsourceShape⟩ := hsourceDecomp
          obtain ⟨words, hwords, hwordslength⟩ := evalSourceWordExpList_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context state.locals hrel.2.1
            (fun current value hcurrent =>
              hlookup context sourceLocals current value hcurrent)
            fields fieldValues hfields
          cases hsourceShape
          cases hwords
          have hshapeListAux : ∀ (fieldList : List (SourceWordExp α))
              (wordList : List α), wordList.length = fieldList.length →
              wordList.map (fun _ => Shape.one) =
                fieldList.map (fun _ => Shape.one) := by
            intro fieldList
            induction fieldList with
            | nil =>
                intro wordList hlength
                cases wordList with
                | nil => rfl
                | cons word words => simp at hlength
            | cons field fieldList ih =>
                intro wordList hlength
                cases wordList with
                | nil => simp at hlength
                | cons word wordList =>
                    simp only [List.map_cons]
                    congr 1
                    exact ih wordList (by simpa using hlength)
          have hshapeList := hshapeListAux fields words hwordslength
          have hsourceFields :
              evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                sourceMemory baseAddress topAddress bytesInWord
                (fields.map SourceWordExp.toExp) =
                some (words.map (fun value => .word value)) := by
            simpa using hfields
          have hshape :
              panShapeMatches
                (panValueShape structs
                  (.rStruct (words.map (fun value => .word value))))
                (.comb (fields.map (fun _ => .one))) = true := by
            rw [← hshapeList]
            have hshapeOneList : ∀ wordList : List α,
                panShapeMatches.panShapeListMatches
                  (wordList.map (fun _ => .one))
                  (wordList.map (fun _ => .one)) = true := by
              intro wordList
              induction wordList with
              | nil => simp [panShapeMatches, panShapeMatches.panShapeListMatches]
              | cons word wordList ih =>
                  simp [panShapeMatches, panShapeMatches.panShapeListMatches, ih]
            simpa [panValueShape, panShapeMatches, Function.comp_def] using
              hshapeOneList words
          let sourceValue : PanValue α :=
            .rStruct (words.map (fun value => .word value))
          let sourceLocals' := updatePanValueMap sourceLocals name sourceValue
          let nextContext := { context with
            vars := (name, (.comb (fields.map (fun _ => .one)),
              allocatedNames context (.comb (fields.map (fun _ => .one))))) ::
              context.vars
            maxVar := context.maxVar +
              Shape.shapeSize (.comb (fields.map (fun _ => .one))) }
          cases hsourceBody :
              evalPanValueProgWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord sourceFuel
                sourceLocals' sourceGlobals sourceMemory body with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hvalue, sourceLocals', sourceValue, hshape,
                hsourceBody] at hsource
          | some bodyResult =>
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.dec name (.comb (fields.map (fun _ => .one)))
                      (.rStruct (fields.map SourceWordExp.toExp)) body) =
                    some (restorePanValueControlLocal name
                      (sourceLocals name) bodyResult) := by
                simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                  evalPanValueExp, evalPanValueExp.evalPanValueExps,
                  hvalue, sourceLocals', sourceValue, hshape, hsourceBody,
                  restorePanValueControlLocal, updatePanValueMap]
              obtain ⟨compiled, hcompileList, hcompiled, hcompiledLength⟩ :=
                compileSourceWordExpList_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hcurrent =>
                    hlookup context sourceLocals current value hcurrent)
                  fields words hsourceFields
              have hflatAux : ∀ (compiledList : List (CrepExp α)),
                  List.flatMap Prod.fst
                    (compiledList.map (fun compiled => ([compiled], Shape.one))) =
                    compiledList := by
                intro compiledList
                induction compiledList with
                | nil => simp
                | cons head tail ih =>
                    simpa only [List.map_cons, List.flatMap_cons,
                      List.singleton_append, List.nil_append] using
                      congrArg (fun values => head :: values) ih
              have hshapeAux : ∀ (compiledList : List (CrepExp α))
                  (wordList : List α), compiledList.length = wordList.length →
                  (compiledList.map (fun compiled => ([compiled], Shape.one))).map
                    Prod.snd = wordList.map (fun _ => Shape.one) := by
                intro compiledList
                induction compiledList with
                | nil =>
                    intro wordList hlength
                    cases wordList with
                    | nil => rfl
                    | cons word words => simp at hlength
                | cons head tail ih =>
                    intro wordList hlength
                    cases wordList with
                    | nil => simp at hlength
                    | cons word wordList =>
                        simp only [List.map_cons]
                        congr 1
                        exact ih wordList (by simpa using hlength)
              have hflat := hflatAux compiled
              have hcompiledShapes := hshapeAux compiled words hcompiledLength
              have hcompile :
                  compileExp context
                      (.rStruct (fields.map SourceWordExp.toExp)) =
                    (compiled, .comb (words.map (fun _ => .one))) := by
                simp only [compileExp]
                rw [hcompileList]
                rw [hflat, hcompiledShapes]
              have hcompileShape :
                  compileExp context
                      (.rStruct (fields.map SourceWordExp.toExp)) =
                    (compiled, .comb (fields.map (fun _ => .one))) := by
                simpa [hshapeList] using hcompile
              have hshapeSizeAux : ∀ (fieldList : List (SourceWordExp α)),
                  Shape.shapeSize (.comb (fieldList.map (fun _ => .one))) =
                    fieldList.length := by
                intro fieldList
                have hfold : ∀ (start : Nat)
                    (shapeFields : List (SourceWordExp α)),
                    (shapeFields.map (fun _ => Shape.one)).foldl
                        (fun total field => total + Shape.shapeSize field) start =
                      start + shapeFields.length := by
                  intro start shapeFields
                  induction shapeFields generalizing start with
                  | nil => simp
                  | cons field shapeFields ih =>
                      simp only [List.map_cons, List.foldl, Shape.shapeSize,
                        List.length_cons]
                      rw [ih (start + 1)]
                      omega
                simpa [Shape.shapeSize] using hfold 0 fieldList
              have hshapeSize := hshapeSizeAux fields
              have hnamesLength :
                  (allocatedNames context
                    (.comb (fields.map (fun _ => .one)))).length =
                    compiled.length := by
                simp [allocatedNames, Shape.shapeSize, hshapeSize,
                  hcompiledLength, hwordslength]
              have hnamesWords :
                  (allocatedNames context
                    (.comb (fields.map (fun _ => .one)))).length = words.length :=
                hnamesLength.trans hcompiledLength
              have hcompileProg :
                  compileProg context
                      (.dec name (.comb (fields.map (fun _ => .one)))
                        (.rStruct (fields.map SourceWordExp.toExp)) body) =
                    nestedDecs
                      (allocatedNames context
                        (.comb (fields.map (fun _ => .one)))) compiled
                      (compileProg nextContext body) := by
                simp [compileProg, hcompileShape, nextContext, hnamesLength]
              rw [hcompileProg] at hcrep
              have hdistinct : CrepDistinctNames
                  (allocatedNames context
                    (.comb (fields.map (fun _ => .one)))) := by
                have hdistinctRange : ∀ (start count : Nat),
                    CrepDistinctNames
                      ((List.range count).map (fun offset => start + offset)) := by
                  have happend : ∀ (entries : List Nat) (value : Nat),
                      CrepDistinctNames entries → value ∉ entries →
                      CrepDistinctNames (entries ++ [value]) := by
                    intro entries value
                    induction entries generalizing value with
                    | nil => intro _ _; simp [CrepDistinctNames]
                    | cons head tail ih =>
                        intro hdistinct hnot
                        rcases hdistinct with ⟨hhead, htail⟩
                        have hheadValue : head ≠ value := by
                          intro heq
                          apply hnot
                          simp [heq]
                        have htailNot : value ∉ tail := by
                          intro hmem
                          apply hnot
                          simp [hmem]
                        have hheadNot : head ∉ tail ++ [value] := by
                          intro hmem
                          simp only [List.mem_append, List.mem_singleton] at hmem
                          rcases hmem with hmem | hmem
                          · exact hhead hmem
                          · exact hheadValue hmem
                        exact ⟨hheadNot, ih value htail htailNot⟩
                  intro start count
                  induction count with
                  | zero => simp [CrepDistinctNames]
                  | succ count ih =>
                      have hnot : start + count ∉
                          (List.range count).map (fun offset => start + offset) := by
                        intro hmem
                        obtain ⟨offset, hoff, heq⟩ := List.mem_map.mp hmem
                        have hofflt : offset < count := List.mem_range.mp hoff
                        omega
                      simpa [List.range_succ, List.map_append] using
                        happend ((List.range count).map (fun offset => start + offset))
                          (start + count) ih hnot
                simpa [allocatedNames] using
                  hdistinctRange (context.maxVar + 1)
                    (Shape.shapeSize (.comb (fields.map (fun _ => .one))))
              obtain ⟨bodyFuel, bodyCrepResult, htargetFuel,
                hnested, hrestoreResult⟩ := crepNestedDecsEval_of_eval
                  functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state
                  (allocatedNames context
                    (.comb (fields.map (fun _ => .one)))) compiled
                  (compileProg nextContext body) crepResult hdistinct
                  hnamesLength hcrep
              have hnot : ∀ temporary ∈
                  allocatedNames context
                    (.comb (fields.map (fun _ => .one))),
                  ∀ expression ∈ compiled,
                    temporary ∉ crepExpVars expression := by
                exact hcompiledFresh context compiled hcompileList
              have hbodyEval := crepNestedDecsEval_body_of_evalExps_stable
                functions crepPrimitive ffi sharedMem baseAddress topAddress
                bodyFuel state
                (allocatedNames context (.comb (fields.map (fun _ => .one))))
                compiled (compileProg nextContext body) bodyCrepResult words
                hnamesLength hnot hcompiled hnested
              have hread := readCrepLocals_updateCrepLocalList
                state.locals
                (allocatedNames context (.comb (fields.map (fun _ => .one))))
                words hnamesWords hdistinct
              have hold : ∀ oldName oldValue oldShape oldSlots,
                  oldName ≠ name →
                  sourceLocals oldName = some oldValue →
                  lookupInfo oldName context.vars = some (oldShape, oldSlots) →
                  panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
                  readCrepLocals
                      (updateCrepLocalList state.locals
                        (allocatedNames context
                          (.comb (fields.map (fun _ => .one)))) words) oldSlots =
                    some (panValueFlatWords oldValue) := by
                intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
                have holdValue := hrel.2.1 oldName oldValue oldShape oldSlots
                  hsourceOld hlookupOld
                have hnotOld : ∀ temporary ∈
                    allocatedNames context
                      (.comb (fields.map (fun _ => .one))),
                    temporary ∉ oldSlots :=
                  fun temporary htemporary =>
                    hfresh context oldName oldShape oldSlots hne hlookupOld
                      temporary htemporary
                have hreadSame := readCrepLocals_updateCrepLocalList_of_not_mem
                  state.locals
                  (allocatedNames context (.comb (fields.map (fun _ => .one))))
                  words oldSlots hnamesWords hnotOld
                exact ⟨holdValue.1, hreadSame.trans holdValue.2⟩
              have hrelBody :
                  panValueCrepStateRel structs nextContext sourceLocals'
                    sourceGlobals sourceMemory
                    { state with
                        locals := (updateCrepLocalList state.locals
                          (allocatedNames context
                            (.comb (fields.map (fun _ => .one)))) words) } := by
                have hrelUpdated :
                    panValueCrepStateRel structs context sourceLocals
                      sourceGlobals sourceMemory
                      { state with
                          locals := updateCrepLocalList state.locals
                            (allocatedNames context
                              (.comb (fields.map (fun _ => .one)))) words } := by
                  refine ⟨hrel.1, ?_, hrel.2.2⟩
                  intro current currentValue currentShape currentSlots hcurrent hlookupCurrent
                  have hne : current ≠ name := by
                    intro heq
                    subst current
                    rw [hname context] at hlookupCurrent
                    cases hlookupCurrent
                  have holdCurrent := hrel.2.1 current currentValue currentShape
                    currentSlots hcurrent hlookupCurrent
                  have hnotCurrent : ∀ temporary ∈
                      allocatedNames context
                        (.comb (fields.map (fun _ => .one))),
                      temporary ∉ currentSlots := by
                    intro temporary htemporary
                    exact hfresh context current currentShape currentSlots hne
                      hlookupCurrent temporary htemporary
                  have hreadCurrent :=
                    readCrepLocals_updateCrepLocalList_of_not_mem state.locals
                      (allocatedNames context
                        (.comb (fields.map (fun _ => .one)))) words currentSlots
                      hnamesWords hnotCurrent
                  exact ⟨holdCurrent.1, hreadCurrent.trans holdCurrent.2⟩
                simpa [nextContext, panValueCrepStateRel, panValueCrepLocalsRel,
                  Shape.shapeSize] using
                  (panValueCrepStateRel_extend structs context sourceLocals
                    sourceLocals' sourceGlobals sourceMemory
                    { state with
                        locals := updateCrepLocalList state.locals
                          (allocatedNames context
                            (.comb (fields.map (fun _ => .one)))) words } name
                    (.comb (fields.map (fun _ => .one)))
                    (allocatedNames context
                      (.comb (fields.map (fun _ => .one)))) sourceValue
                    (by rfl) hshape
                    (by simpa [sourceValue, panValueFlatWords_rStruct_word_list] using hread)
                    hold hrelUpdated)
              have hbodyRelFinal := hbody nextContext structs sourceFunctions
                functions sourceLocals' sourceGlobals sourceMemory
                { state with
                    locals := (updateCrepLocalList state.locals
                      (allocatedNames context
                        (.comb (fields.map (fun _ => .one)))) words) }
                primitive sourceHandler crepPrimitive ffi sharedMem
                baseAddress topAddress bytesInWord sourceFuel bodyFuel
                exceptionRel bodyResult bodyCrepResult hrelBody hsourceBody
                hbodyEval
              have houterRel := panValueCrepControlRel_restore_declaration
                structs context (sourceLocals name) state name
                (.comb (fields.map (fun _ => .one)))
                (allocatedNames context
                  (.comb (fields.map (fun _ => .one))))
                (hname context)
                (fun oldName oldShape oldSlots hne hlookupOld temporary htemp =>
                  hfresh context oldName oldShape oldSlots hne hlookupOld
                    temporary htemp)
                exceptionRel bodyResult bodyCrepResult hbodyRelFinal
              have hsourceEq :=
                Option.some.inj (hsourceExpected.symm.trans hsource)
              cases hsourceEq
              rw [hrestoreResult] at houterRel
              exact houterRel

end Flapjack
