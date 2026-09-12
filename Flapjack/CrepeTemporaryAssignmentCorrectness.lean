import Flapjack.CrepeAssignmentSequenceCorrectness
import Flapjack.CrepeDeclarationRelation
import Flapjack.CrepeNestedDecsStability
import Flapjack.CrepeSourceWordRecordShapeCorrectness

/-!
Reusable evaluator facts for the temporary path of flattened assignments.
Fresh declarations first bind the compiled values, after which the compiler
assigns the destination slots from fresh variables and restores those
variables on exit.
-/

namespace Flapjack

def restoredCrepLocals (locals result : Nat → Option α) : List Nat →
    Nat → Option α
  | [], current => result current
  | name :: names, current =>
      if current = name then locals current
      else restoredCrepLocals locals result names current

theorem updateCrepLocalList_of_mem_eq
    (locals locals' : Nat → Option α)
    (names : List Nat) (values : List α) (current : Nat)
    (hlength : names.length = values.length)
    (hdistinct : CrepDistinctNames names)
    (hmem : current ∈ names) :
    updateCrepLocalList locals names values current =
      updateCrepLocalList locals' names values current := by
  induction names generalizing locals locals' values with
  | nil => simp at hmem
  | cons name names ih =>
      rcases hdistinct with ⟨hnot, htailDistinct⟩
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hlengthTail : names.length = values.length := by
            simp only [List.length_cons] at hlength
            omega
          by_cases hcurrent : current = name
          · have hreadLeft := updateCrepLocalList_of_not_mem
                (updateCrepLocal locals name value) names values name
                hlengthTail hnot
            have hreadRight := updateCrepLocalList_of_not_mem
                (updateCrepLocal locals' name value) names values name
                hlengthTail hnot
            simp [updateCrepLocalList, updateCrepLocal, hcurrent,
              hreadLeft, hreadRight]
          · have htail : current ∈ names := by
              simpa [hcurrent] using hmem
            simp only [updateCrepLocalList]
            exact ih (locals := updateCrepLocal locals name value)
              (locals' := updateCrepLocal locals' name value)
              (values := values) hlengthTail htailDistinct htail

set_option linter.unusedSimpArgs false in
theorem restoreCrepResultList_normal_explicit
    [OfNat α 0]
    (locals resultLocals : Nat → Option α) (memory : α → Option α)
    (names : List Nat) (globals : α → Option α := fun _ => none) :
    restoreCrepResultList locals names
        (.normal (CrepState.mk resultLocals memory globals)) =
      .normal (CrepState.mk (restoredCrepLocals locals resultLocals names)
        memory globals) := by
  induction names generalizing locals resultLocals with
  | nil =>
      simp [restoreCrepResultList, restoredCrepLocals]
  | cons name names ih =>
      have htail := ih (locals := updateCrepLocal locals name 0)
        (resultLocals := resultLocals)
      simp only [restoreCrepResultList, restoreCrepResult, htail]
      have hlocals :
          restoreCrepLocal
              (restoredCrepLocals (updateCrepLocal locals name 0)
                resultLocals names)
              name (locals name) =
            restoredCrepLocals locals resultLocals (name :: names) := by
        funext current
        by_cases hcurrent : current = name
        · simp [restoredCrepLocals, restoreCrepLocal, updateCrepLocal, hcurrent]
        · have hinv : ∀ (tailNames : List Nat),
              restoredCrepLocals (updateCrepLocal locals name 0)
                resultLocals tailNames current =
              restoredCrepLocals locals resultLocals tailNames current := by
            intro tailNames
            induction tailNames with
            | nil => rfl
            | cons tailName tailNames ih =>
                by_cases htail : current = tailName
                · have htailNe : tailName ≠ name := by
                    intro heq
                    apply hcurrent
                    simp [htail, heq]
                  simp [restoredCrepLocals, htail, updateCrepLocal,
                    htailNe]
                · simp [restoredCrepLocals, htail, ih, updateCrepLocal,
                    hcurrent]
          simp [restoredCrepLocals, restoreCrepLocal, hcurrent, hinv names]
      exact congrArg CrepControlResult.normal
        (congrArg (fun currentLocals =>
          ({ locals := currentLocals, memory := memory, globals := globals } :
            CrepState α)) hlocals)

theorem restoreCrepResultList_normal_updateList
    [OfNat α 0]
    (locals resultLocals : Nat → Option α)
    (temporarySlots destinationSlots : List Nat) (values : List α)
    (memory globals : α → Option α)
    (htemporaryLength : temporarySlots.length = values.length)
    (hdestinationLength : destinationSlots.length = values.length)
    (hdestinationDistinct : CrepDistinctNames destinationSlots)
    (hnoalias : ∀ temporary ∈ temporarySlots,
      temporary ∉ destinationSlots)
    (hresult : resultLocals =
      updateCrepLocalList
        (updateCrepLocalList locals temporarySlots values)
        destinationSlots values) :
    restoreCrepResultList locals temporarySlots
        (.normal (CrepState.mk resultLocals memory globals)) =
      .normal (CrepState.mk (updateCrepLocalList locals destinationSlots values)
        memory globals) := by
  have hrestored :
      restoredCrepLocals locals resultLocals temporarySlots =
        updateCrepLocalList locals destinationSlots values := by
    have hrestoreMem : ∀ (current : Nat) (names : List Nat),
        current ∈ names →
        restoredCrepLocals locals resultLocals names current = locals current := by
      intro current names
      induction names with
      | nil => simp
      | cons name names ih =>
          intro hmem
          by_cases hcurrent : current = name
          · simp [restoredCrepLocals, hcurrent]
          · have htail : current ∈ names := by
              simpa [hcurrent] using hmem
            simp [restoredCrepLocals, hcurrent, ih htail]
    have hrestoreNot : ∀ (current : Nat) (names : List Nat),
        current ∉ names →
        restoredCrepLocals locals resultLocals names current =
          resultLocals current := by
      intro current names
      induction names with
      | nil => simp [restoredCrepLocals]
      | cons name names ih =>
          intro hmem
          have hcurrent : current ≠ name := by
            intro heq
            apply hmem
            simp [heq]
          have htail : current ∉ names := by
            intro htail
            exact hmem (by simp [htail])
          simp [restoredCrepLocals, hcurrent, ih htail]
    funext current
    by_cases htemporary : current ∈ temporarySlots
    · have hdestination : current ∉ destinationSlots := by
        intro hmem
        exact hnoalias current htemporary hmem
      have hreadDestination := updateCrepLocalList_of_not_mem
        locals destinationSlots values current hdestinationLength
        hdestination
      rw [hrestoreMem current temporarySlots htemporary]
      exact hreadDestination.symm
    · have hreadTemporary := updateCrepLocalList_of_not_mem
        locals temporarySlots values current htemporaryLength htemporary
      rw [hrestoreNot current temporarySlots htemporary, hresult]
      by_cases hdestination : current ∈ destinationSlots
      · exact updateCrepLocalList_of_mem_eq
          (updateCrepLocalList locals temporarySlots values) locals
          destinationSlots values current hdestinationLength
          hdestinationDistinct hdestination
      · have hreadDestination := updateCrepLocalList_of_not_mem
          (updateCrepLocalList locals temporarySlots values)
          destinationSlots values current hdestinationLength hdestination
        have hreadDestination' := updateCrepLocalList_of_not_mem
          locals destinationSlots values current hdestinationLength hdestination
        rw [hreadDestination, hreadTemporary, hreadDestination']
  rw [restoreCrepResultList_normal_explicit locals resultLocals memory
    temporarySlots globals]
  simp [hrestored]

theorem evalCrepFullExps_varList_updateCrepLocalList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α)
    (names : List Nat) (values : List α)
    (hlength : names.length = values.length)
    (hdistinct : CrepDistinctNames names) :
    evalCrepFullExps
        (updateCrepLocalList locals names values) memory
        baseAddress topAddress (names.map (fun name => .var name)) =
      some values := by
  have hread := readCrepLocals_updateCrepLocalList locals names values
    hlength hdistinct
  have hvars : ∀ (current : Nat → Option α) (currentNames : List Nat),
      evalCrepFullExps current memory baseAddress topAddress
          (currentNames.map (fun name => .var name)) =
        readCrepLocals current currentNames := by
    intro current currentNames
    induction currentNames with
    | nil => simp [evalCrepFullExps, readCrepLocals]
    | cons name currentNames ih =>
        simp only [List.map_cons, evalCrepFullExps, evalCrepFullExp,
          readCrepLocals]
        rw [ih]
  rw [hvars]
  exact hread

theorem evalCrepFullExpsState_varList_updateCrepLocalList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (names : List Nat) (values : List α)
    (hlength : names.length = values.length)
    (hdistinct : CrepDistinctNames names) :
    evalCrepFullExpsState
        { state with locals := updateCrepLocalList state.locals names values }
        baseAddress topAddress (names.map (fun name => .var name)) =
      some values := by
  have hread := readCrepLocals_updateCrepLocalList state.locals names values
    hlength hdistinct
  have hvars : ∀ (current : CrepState α) (currentNames : List Nat),
      evalCrepFullExpsState current baseAddress topAddress
          (currentNames.map (fun name => .var name)) =
        readCrepLocals current.locals currentNames := by
    intro current currentNames
    induction currentNames with
    | nil => simp [evalCrepFullExpsState, readCrepLocals]
    | cons name currentNames ih =>
        simp only [List.map_cons, evalCrepFullExpsState,
          evalCrepFullExpState, readCrepLocals]
        rw [ih]
  rw [hvars]
  exact hread

theorem evalCrepFullProg_nestedDecs_assignList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (names : List Nat) (expressions : List (CrepExp α)) (body : CrepProg α)
    (values : List α) (result : CrepControlResult α)
    (hlength : names.length = expressions.length)
    (hdistinct : CrepDistinctNames names)
    (hnot : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names expressions body) =
      some (restoreCrepResultList state.locals names result) := by
  have hnested := crepNestedDecsEval_of_evalExps_stable functions primitive ffi sharedMem
    baseAddress topAddress fuel state names expressions body result values
    hlength hnot heval hbody
  exact evalCrepFullProg_nestedDecs_of_eval functions primitive ffi sharedMem
    baseAddress topAddress fuel state names expressions body result hdistinct hnested

theorem crepAssignZipWith_map_right {α : Type u}
    (slots temporarySlots : List Nat) :
    List.zipWith
        (fun slot (expression : CrepExp α) => CrepProg.assign slot expression)
        slots (temporarySlots.map (fun temporary => CrepExp.var temporary)) =
      List.zipWith
        (fun slot (temporary : Nat) =>
          CrepProg.assign slot (CrepExp.var temporary)) slots temporarySlots := by
  induction slots generalizing temporarySlots with
  | nil => rfl
  | cons slot slots ih =>
      cases temporarySlots with
      | nil => rfl
      | cons temporary temporarySlots =>
          simp only [List.map_cons, List.zipWith]
          congr 1
          exact ih (temporarySlots := temporarySlots)

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_local_assign_record_source_word_temporary_general
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
    (name : VarName) (slots temporarySlots : List Nat)
    (oldValues values : List α)
    (fields : List (SourceWordExp α)) (compiled : List (CrepExp α))
    (hlookup : lookupInfo name context.vars =
      some (.comb (values.map (fun _ => .one)), slots))
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hlocals : sourceLocals name =
      some (.rStruct (oldValues.map (fun value => .word value))))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panShapeMatches
      (panValueShape structs (.rStruct (values.map (fun value => .word value))))
      (panValueShape structs (.rStruct (oldValues.map (fun value => .word value)))) =
      true)
    (hcompile : compileExp context
      (.rStruct (fields.map SourceWordExp.toExp)) =
      (compiled, .comb (values.map (fun _ => .one))))
    (hcompiledLength : compiled.length = values.length)
    (hcompiled : evalCrepFullExps state.locals state.memory
      baseAddress topAddress compiled = some values)
    (hnotDistinct : distinctLists slots (compiled.flatMap crepExpVars) = false)
    (hfreshNames : temporarySlots = freshNames context slots.length 1)
    (htemporaryLength : temporarySlots.length = values.length)
    (htemporaryDistinct : CrepDistinctNames temporarySlots)
    (hcompiledFresh : ∀ temporary ∈ temporarySlots,
      ∀ expression ∈ compiled, temporary ∉ crepExpVars expression)
    (hnoOverlap : ∀ slot ∈ slots, ∀ temporary ∈ temporarySlots,
      slot ≠ temporary)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name
        (.rStruct (fields.map SourceWordExp.toExp))) =
      some (.normal
        (updatePanValueMap sourceLocals name
          (.rStruct (values.map (fun value => .word value))))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (targetFuel + slots.length + 1 + temporarySlots.length) state
      (compileProg context
        (.assign .local name
          (.rStruct (fields.map SourceWordExp.toExp)))) =
      some (.normal { state with
        locals := updateCrepLocalList state.locals slots values }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name
        (.rStruct (values.map (fun value => .word value))))
      sourceGlobals sourceMemory
      { state with locals := updateCrepLocalList state.locals slots values } := by
  have hcompileProg :
      compileProg context
        (.assign .local name (.rStruct (fields.map SourceWordExp.toExp))) =
        nestedDecs temporarySlots compiled
          (crepNestedSeq (slots.zipWith
        (fun slot temporary => .assign slot (.var temporary))
          temporarySlots)) := by
    rw [hfreshNames]
    simp [compileProg, hlookup, hcompile, hlength, hcompiledLength,
      hnotDistinct, freshNames, nestedDecs, crepNestedSeq]
  have htempSlotLength : slots.length = temporarySlots.length := by
    exact hlength.trans htemporaryLength.symm
  have hbodyEval := evalCrepFullExps_varList_updateCrepLocalList
    state.locals state.memory baseAddress topAddress temporarySlots values
    htemporaryLength htemporaryDistinct
  have hbody :
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress (targetFuel + slots.length + 1)
        { state with locals := updateCrepLocalList state.locals temporarySlots values }
        (crepNestedSeq (slots.zipWith
          (fun slot temporary => .assign slot (.var temporary))
          temporarySlots)) =
      some (.normal { state with
        locals := updateCrepLocalList
          (updateCrepLocalList state.locals temporarySlots values)
          slots values }) := by
    have hassign := evalCrepFullProg_assignList functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { state with
          locals := updateCrepLocalList state.locals temporarySlots values }
      slots (temporarySlots.map (fun temporary => .var temporary)) values
      (by simpa using htempSlotLength) hdistinct
      (by
        intro slot hslot expression hexpression
        obtain ⟨temporary, htemporaryMem, htemporaryEq⟩ :=
          List.mem_map.1 hexpression
        subst expression
        simpa [crepExpVars] using hnoOverlap slot hslot temporary htemporaryMem)
      hbodyEval
    rw [crepAssignZipWith_map_right] at hassign
    exact hassign
  have hnested := evalCrepFullProg_nestedDecs_assignList
    functions crepPrimitive ffi sharedMem baseAddress topAddress
    (targetFuel + slots.length + 1) state temporarySlots compiled
    (crepNestedSeq (slots.zipWith
      (fun slot temporary => .assign slot (.var temporary)) temporarySlots))
    values
    (.normal { state with
      locals := updateCrepLocalList
        (updateCrepLocalList state.locals temporarySlots values) slots values })
    (by exact htemporaryLength.trans hcompiledLength.symm)
    htemporaryDistinct hcompiledFresh hcompiled hbody
  have hrestored := restoreCrepResultList_normal_updateList
    state.locals
    (updateCrepLocalList
      (updateCrepLocalList state.locals temporarySlots values) slots values)
    temporarySlots slots values state.memory state.globals
    htemporaryLength hlength hdistinct
    (by
      intro temporary htemporaryMem hslot
      exact (hnoOverlap temporary hslot temporary htemporaryMem) rfl)
    rfl
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid, hlocals,
      panValueAssignmentValid, updatePanValueMap]
  constructor
  · rw [hcompileProg]
    calc
      evalCrepFullProg functions crepPrimitive ffi sharedMem
          baseAddress topAddress
          (targetFuel + slots.length + 1 + temporarySlots.length) state
          (nestedDecs temporarySlots compiled
            (crepNestedSeq (slots.zipWith
              (fun slot temporary => .assign slot (.var temporary))
              temporarySlots))) =
          some (restoreCrepResultList state.locals temporarySlots
            (.normal { state with
              locals := updateCrepLocalList
                (updateCrepLocalList state.locals temporarySlots values) slots values })) := by
            simpa [Nat.add_assoc] using hnested
      _ = some (.normal ({ state with
          locals := updateCrepLocalList state.locals slots values } : CrepState α)) := by
            rw [hrestored]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word_list structs context sourceLocals
      state.locals name slots values hrel.2.1 hlookup hlength hdistinct hnoalias

end Flapjack
