import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanCommonProps

/-! Nonvacuous checks for the HOL `state_rel_def`, `state_rel_structs`,
`state_rel_globals`, and `locals_rel_def` ports in
`Flapjack/Pancake/Proofs/PanToCrep.lean`.  Each relation has a satisfying
fixture and a rejected fixture. A nonempty target code map is also tied to the
runtime function list and carried through target Skip evaluation. -/

namespace Flapjack.Test.PanToCrepStateRelParity

open Flapjack
open Flapjack.Pancake.PanLang

def noNatCells : Nat → PanWordLab Nat := fun _ => .word 0
def noPanValueCells : Nat → Option (PanValue Nat) := fun _ => some (.word 0)
def noMemaddrs : Nat → Bool := fun _ => false

def sourceState : PanSemState Nat (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := noPanValueCells
    memaddrs := noMemaddrs
    sharedMemaddrs := noMemaddrs
    clock := 5
    be := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def targetState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := noNatCells
    memaddrs := noMemaddrs
    shMemaddrs := noMemaddrs
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 5
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def skipCodeMap : FiniteMap String (List Nat × CrepProg Nat) :=
  FUPDATE_LIST FEMPTY [("id", ([], .skip))]

def skipCodeRuntime : CrepRuntimeState Nat Unit :=
  { targetState with code := skipCodeMap }

theorem skipCodeMap_has_runtime_entry :
    FLOOKUP skipCodeRuntime.code "id" = some ([], (CrepProg.skip : CrepProg Nat)) ∧
    lookupCrepRuntimeCode "id" [] skipCodeRuntime.code = some (.skip, fun _ => none) := by
  constructor
  · simp [skipCodeRuntime, skipCodeMap, FUPDATE_LIST, FUPDATE, FLOOKUP]
  · simp [lookupCrepRuntimeCode, lookupCrepHolCode, skipCodeRuntime, skipCodeMap,
      FUPDATE_LIST, FUPDATE, FLOOKUP]
    funext name
    rfl

def skipCodeContext : PanToCrepProofContext Nat :=
  { vars := FEMPTY
    funcs := FUPDATE FEMPTY ("id", ([], Shape.one))
    eids := FEMPTY
    vmax := 0 }

def skipSourceCode : PanSemCodeMap Nat :=
  [("id", ([], .skip, Shape.one))]

def skipSourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with code := skipSourceCode }

theorem skipCodeRelFixture :
    codeRel skipCodeContext (panSemCodeAsLookup skipSourceState.code)
      skipCodeRuntime.code := by
  intro function variableShapes program returnShape hlookup
  by_cases hname : function = "id"
  · subst function
    have hvalues : ([], Prog.skip, Shape.one) =
        (variableShapes, program, returnShape) := by
      simpa [skipSourceState, skipSourceCode, panSemCodeAsLookup,
        panSemCodeLookup, lookupInfo, FLOOKUP] using hlookup
    rcases hvalues with ⟨rfl, rfl, rfl⟩
    simp [skipCodeContext, skipCodeRuntime, skipCodeMap, FUPDATE_LIST, FUPDATE,
      FLOOKUP, compileCodeRelProg, compileProgHOL, localisedProg,
      Shape.shapeSize]
  · have hid : ("id" : String) ≠ function := fun heq => hname heq.symm
    simp [skipSourceState, skipSourceCode, panSemCodeAsLookup,
      panSemCodeLookup, lookupInfo, FLOOKUP, hid] at hlookup

def nonEmptyGlobalsSourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with globals := fun _ => some (.word 0) }

def structMemorySourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with memory := fun _ => some (.rStruct []) }

theorem stateRel_satisfied : stateRel sourceState targetState := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  simp [sourceState, targetState, noPanValueCells, noNatCells, panTheWord]

theorem skipCodeRuntime_relates :
    stateRel sourceState skipCodeRuntime := by
  simpa [stateRel, skipCodeRuntime, targetState] using
    stateRel_satisfied

theorem skipCodeRelEmptyLocalsFixture :
    codeRel skipCodeContext
      (panSemCodeAsLookup (panEmptyLocals skipSourceState).code)
      (clearCrepRuntimeLocals skipCodeRuntime).code :=
  codeRelEmptyLocals skipCodeContext skipSourceState skipCodeRuntime
    skipCodeRelFixture

def skipCodeLookupGuard : Bool :=
  (FLOOKUP skipCodeRuntime.code "id").isSome &&
    (lookupCrepRuntimeCode "id" [] skipCodeRuntime.code).isSome

theorem stateRel_structs_fixture : sourceState.structs = [] :=
  stateRel_structs sourceState targetState stateRel_satisfied

theorem stateRel_globals_fixture :
    sourceState.globals = (FEMPTY : FiniteMap VarName (PanValue Nat)) :=
  stateRel_globals sourceState targetState stateRel_satisfied

theorem rejectsNonEmptyGlobals :
    ¬ stateRel nonEmptyGlobalsSourceState targetState := by
  intro hrel
  have hglobals := stateRel_globals nonEmptyGlobalsSourceState targetState hrel
  have h0 := congrFun hglobals "x"
  simp [nonEmptyGlobalsSourceState, sourceState, FEMPTY] at h0

theorem rejectsStructMemory :
    ¬ stateRel structMemorySourceState targetState := by
  intro hrel
  have h0 := congrFun hrel.1 0
  simp [structMemorySourceState, sourceState, targetState, noNatCells, panTheWord] at h0

def oneVarContext : PanToCrepProofContext Nat :=
  { vars := FUPDATE FEMPTY ("x", (Shape.one, [0]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 0 }

def sourceLocals : FiniteMap String (PanValue Nat) :=
  FUPDATE FEMPTY ("x", .word 5)

def targetLocals : FiniteMap Nat (PanWordLab Nat) :=
  FUPDATE FEMPTY (0, .word 5)

theorem localsRel_satisfied : localsRel oneVarContext sourceLocals targetLocals := by
  refine ⟨⟨?_, ?_⟩, ⟨Nat.zero_le 0, ?_⟩, ?_⟩
  · intro x a xs hlookup
    simp only [oneVarContext, FLOOKUP, FUPDATE] at hlookup
    split at hlookup
    · simp only [Option.some.injEq, Prod.mk.injEq] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      simp
    · simp [FEMPTY] at hlookup
  · intro x y a b xs ys hx hy _hinter
    simp only [oneVarContext, FLOOKUP, FUPDATE] at hx hy
    split at hx
    · rename_i hxcond
      have hx_eq : ("x" : String) = x := beq_iff_eq.mp hxcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      split at hy
      · rename_i hycond
        have hy_eq : ("x" : String) = y := beq_iff_eq.mp hycond
        rw [← hx_eq, ← hy_eq]
      · simp [FEMPTY] at hy
    · simp [FEMPTY] at hx
  · intro v a xs hlookup x hmem
    simp only [oneVarContext, FLOOKUP, FUPDATE] at hlookup
    split at hlookup
    · simp only [Option.some.injEq, Prod.mk.injEq] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      simp only [List.mem_singleton, oneVarContext] at hmem ⊢
      omega
    · simp [FEMPTY] at hlookup
  · intro vname v hlookup
    simp only [sourceLocals, FLOOKUP, FUPDATE] at hlookup
    split at hlookup
    · rename_i hvcond
      have hv_eq : ("x" : String) = vname := beq_iff_eq.mp hvcond
      simp only [Option.some.injEq] at hlookup
      rcases hlookup with rfl
      refine ⟨[0], [.word 5], ?_, ?_, ?_, ?_⟩
      · rw [← hv_eq]
        simp [oneVarContext, FLOOKUP, FUPDATE, panValueShape]
      · simp [targetLocals, FLOOKUP, FUPDATE]
      · simp [panValueFlatten_word]
      · simp [panValueShape, isWfShape]
    · simp [FEMPTY] at hlookup

def compileExpNotMemSourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with locals := sourceLocals }

def compileExpNotMemTargetState : CrepRuntimeState Nat Unit :=
  { targetState with locals := targetLocals }

def compileExpNotMemExpression : Exp Nat :=
  .op .add [.var .local "x", .const 7]

/-- The fixture exercises a nested `exps` traversal through an operation and
    supplies the actual HOL-shaped local, state, code, and locals relations. -/
theorem compileExpNotMemLoadGlob_fixture :
    CrepExp.loadGlob 17 ∉
      ([.op .add [.var 0, .const 7]] : List (CrepExp Nat)).flatMap crepExps := by
  apply compileExpNotMemLoadGlob oneVarContext compileExpNotMemExpression
    compileExpNotMemSourceState compileExpNotMemTargetState
    [.op .add [.var 0, .const 7]] .one 17
  · simp [compileExpNotMemExpression,
      compileExpHOL, oneVarContext, FLOOKUP, FUPDATE, compileExpHOL.compileExpListHOL,
      cexpHeads]
  · simpa [stateRel, compileExpNotMemSourceState, compileExpNotMemTargetState,
      sourceState, targetState] using
      stateRel_satisfied
  · intro function variableShapes program returnShape hlookup
    simp [compileExpNotMemSourceState, sourceState, panSemCodeAsLookup, panSemCodeLookup, lookupInfo,
      FLOOKUP] at hlookup
  · exact localsRel_satisfied

/-- The exact lookup theorem recovers the concrete slot, flattened word, and
    well-formed shape for the one-word local in `localsRel_satisfied`. -/
theorem localsRelLookupCtxt_fixture :
    ∃ slots,
      FLOOKUP oneVarContext.vars "x" = some (.one, slots) ∧
      slots.length = 1 ∧
      slots.mapM (FLOOKUP targetLocals) = some [.word 5] ∧
      isWfShape [] .one = true := by
  obtain ⟨slots, hcontext, _, hmap, hwf⟩ :=
    localsRelLookupCtxt oneVarContext sourceLocals targetLocals "x" (.word 5)
      localsRel_satisfied (by simp [sourceLocals, FLOOKUP, FUPDATE])
  have hslots : slots = [0] := by
    simpa [oneVarContext, FLOOKUP, FUPDATE, panValueShape] using hcontext.symm
  subst slots
  refine ⟨[0], ?_, ?_, ?_, ?_⟩
  · simp [oneVarContext, FLOOKUP, FUPDATE]
  · simp
  · simpa [panValueFlatten_word] using hmap
  · simpa [panValueShape] using hwf

theorem rejectsUnmappedLocal :
    ¬ localsRel { oneVarContext with vars := FEMPTY } sourceLocals targetLocals := by
  intro hrel
  have hx := hrel.2.2 "x" (.word 5) (by simp [sourceLocals, FLOOKUP, FUPDATE])
  obtain ⟨ns, vs, hctxt, _⟩ := hx
  simp [FLOOKUP, FEMPTY] at hctxt

def contextVarGuard : Bool :=
  match FLOOKUP oneVarContext.vars "x" with
  | some (.one, [0]) => true
  | _ => false

def localMapGuard : Bool :=
  ([0].mapM (FLOOKUP targetLocals) == some [.word 5]) &&
    (panValueFlatten (.word 5) == [5])

def localsRelLookupCtxtGuard : Bool :=
  match FLOOKUP oneVarContext.vars "x" with
  | some (.one, slots) =>
      (slots == [0]) && slots.length == 1 &&
        ([0].mapM (FLOOKUP targetLocals) == some [.word 5]) && isWfShape [] .one
  | _ => false

/-- Exact `ValueHOL` fixture for HOL
`is_wf_shape_nil_length_flatten` (`pan_to_crepProofScript.sml:2469`). -/
def iwfStruct : ValueHOL 64 := .rStruct [.val (.word 1), .val (.word 2)]

theorem isWfShapeExactHOL_length_flatten_fixture :
    (flattenHOL iwfStruct).length = sizeOfShapeHOL (shapeOfHOLExact iwfStruct) :=
  isWfShapeExactHOL_length_flatten iwfStruct (flattenHOL iwfStruct)
    (by simp [iwfStruct, shapeOfHOLExact, isWfShapeExactHOL])
    (by intro h; simp [iwfStruct, shapeOfHOLExact, sizeOfShapeHOL] at h)
    (by intro _; rfl)

def isWfShapeNilLengthFlattenGuard : Bool :=
  (flattenHOL iwfStruct).length == sizeOfShapeHOL (shapeOfHOLExact iwfStruct) &&
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact iwfStruct)

/-! The following related-state fixture uses the same nonempty RV64 word cell
as the direct HOL-EVAL rows `state_rel_source_byte_little`,
`state_rel_source_byte_domain_failure`, and `state_rel_source_word32_little` in
`scripts/hol-probes/pan_sem_state_eval_probe.out`. The production source read
must derive its memory, `memaddrs`, and byte order from `sourceMemoryState`. -/

private abbrev Word64 := RiscV.Word 64

def stateRelMemoryWord : Word64 := BitVec.ofNat 64 0x1122334455667788

def stateRelMemory : Word64 → Word64 := fun address =>
  if address == 0 then stateRelMemoryWord else 0

def sourceMemoryState : PanSemState Word64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun address => some (.word (stateRelMemory address))
    memaddrs := fun address => address == 0
    sharedMemaddrs := fun _ => false
    clock := 3
    be := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def targetMemoryState : CrepRuntimeState Word64 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := fun _ => none
    memory := fun address => .word (stateRelMemory address)
    memaddrs := fun address => address == 0
    shMemaddrs := fun _ => false
    memoryModel := panSemBitVec64WordModel
    bytesInWord := 8
    ffiContext :=
      { sharedDomain := fun _ => false
        byteAlign := fun address => address
        bigEndian := false
        wordToBytes := fun _ _ => []
        wordOfBytes := fun _ _ => 0
        wordToByte := fun _ => 0
        byteToWord := fun _ => 0
        valueToNat := fun _ => 0 }
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

theorem memoryStateRel : stateRel sourceMemoryState targetMemoryState := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  simp [sourceMemoryState, targetMemoryState, stateRelMemory, panTheWord]

def stateRelSourceByteOracleCase : Bool :=
  match evalPanSemStateExp sourceMemoryState (.loadByte (.const 0)) with
  | some (.word value) => value == BitVec.ofNat 64 136
  | _ => false

def stateRelSourceByteRejectedDomainCase : Bool :=
  match evalPanSemStateExp { sourceMemoryState with memaddrs := fun _ => false }
      (.loadByte (.const 0)) with
  | none => true
  | _ => false

def stateRelSourceWord32OracleCase : Bool :=
  match evalPanSemStateExp sourceMemoryState (.load32 (.const 0)) with
  | some (.word value) => value == BitVec.ofNat 64 0x55667788
  | _ => false

def stateRelSourceWord32RejectedAlignmentCase : Bool :=
  match evalPanSemStateExp sourceMemoryState (.load32 (.const 1)) with
  | none => true
  | _ => false

example : evalPanSemStateExp sourceMemoryState (.loadByte (.const 0)) =
    (panMemLoadByteHOL (width := 64)
      (fun address => match targetMemoryState.memory address with
        | .word value => .word value)
      (fun address =>
        (sourceMemoryState.memaddrs address &&
          panValueWordDefined sourceMemoryState.memory address) = true)
      sourceMemoryState.be 0).map
        (fun byte => PanValue.word (BitVec.ofNat 64 byte.toNat)) :=
  panToCrepSourceLoadByteHOLCase sourceMemoryState targetMemoryState 0 memoryStateRel

example : evalPanSemStateExp sourceMemoryState (.load32 (.const 0)) =
    (panMemLoad32HOL (width := 64)
      (fun address => match targetMemoryState.memory address with
        | .word value => .word value)
      (fun address =>
        (sourceMemoryState.memaddrs address &&
          panValueWordDefined sourceMemoryState.memory address) = true)
      sourceMemoryState.be 0).map
        (fun value => PanValue.word (BitVec.ofNat 64 value.toNat)) :=
  panToCrepSourceLoad32HOLCase sourceMemoryState targetMemoryState 0 memoryStateRel

def runChecks : IO Bool := do
  let checks := [
    ("HOL state_rel satisfying fixture", true),
    ("HOL state_rel_structs and state_rel_globals", true),
    ("HOL state_rel rejects nonempty globals", true),
    ("HOL state_rel rejects struct-valued memory", true),
    ("HOL locals_rel satisfying fixture", contextVarGuard && localMapGuard),
    ("HOL locals_rel_lookup_ctxt exact slot, flattened value, and shape",
      localsRelLookupCtxtGuard),
    ("HOL Crep code field matches a nonempty runtime function and survives Skip",
      skipCodeLookupGuard),
    ("HOL locals_rel rejects unmapped local", true),
    ("HOL exact is_wf_shape_nil_length_flatten over ValueHOL",
      isWfShapeNilLengthFlattenGuard),
    ("HOL state_rel source LoadByte uses related nonempty memory",
      stateRelSourceByteOracleCase),
    ("HOL state_rel source LoadByte rejects outside memaddrs",
      stateRelSourceByteRejectedDomainCase),
    ("HOL state_rel source Load32 uses related nonempty memory",
      stateRelSourceWord32OracleCase),
    ("HOL state_rel source Load32 rejects misaligned addresses",
      stateRelSourceWord32RejectedAlignmentCase)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepStateRelParity
