import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanCommonProps

/-! Nonvacuous checks for the HOL `state_rel_def`, `state_rel_structs`,
`state_rel_globals`, and `locals_rel_def` ports in
`Flapjack/Pancake/Proofs/PanToCrep.lean`.  Each relation has a satisfying
fixture and a rejected fixture. -/

namespace Flapjack.Test.PanToCrepStateRelParity

open Flapjack

def noNatCells : Nat → Option Nat := fun _ => none
def noPanValueCells : Nat → Option (PanValue Nat) := fun _ => none
def noMemaddrs : Nat → Bool := fun _ => false

def sourceState : PanSemState Nat (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := fun _ => none
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
    functions := []
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

def nonEmptyGlobalsSourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with globals := fun _ => some (.word 0) }

def structMemorySourceState : PanSemState Nat (FfiState Unit) :=
  { sourceState with memory := fun _ => some (.rStruct []) }

theorem stateRel_satisfied : stateRel sourceState targetState := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  funext address
  simp [sourceState, targetState, noPanValueCells, noNatCells]

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
  simp [structMemorySourceState, sourceState, targetState, noNatCells] at h0

def oneVarContext : PanToCrepProofContext Nat :=
  { vars := FUPDATE FEMPTY ("x", (Shape.one, [0]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 0 }

def sourceLocals : FiniteMap String (PanValue Nat) :=
  FUPDATE FEMPTY ("x", .word 5)

def targetLocals : FiniteMap Nat Nat :=
  FUPDATE FEMPTY (0, 5)

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
      refine ⟨[0], [5], ?_, ?_, ?_, ?_⟩
      · rw [← hv_eq]
        simp [oneVarContext, FLOOKUP, FUPDATE, panValueShape]
      · simp [targetLocals, FLOOKUP, FUPDATE]
      · simp [panValueFlatten_word]
      · simp [panValueShape, isWfShape]
    · simp [FEMPTY] at hlookup

/-- The exact lookup theorem recovers the concrete slot, flattened word, and
    well-formed shape for the one-word local in `localsRel_satisfied`. -/
theorem localsRelLookupCtxt_fixture :
    ∃ slots,
      FLOOKUP oneVarContext.vars "x" = some (.one, slots) ∧
      slots.length = 1 ∧
      slots.mapM (FLOOKUP targetLocals) = some [5] ∧
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
  · simpa only [panValueFlatten_word] using hmap
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
  ([0].mapM (FLOOKUP targetLocals) == some [5]) &&
    (panValueFlatten (.word 5) == [5])

def localsRelLookupCtxtGuard : Bool :=
  match FLOOKUP oneVarContext.vars "x" with
  | some (.one, slots) =>
      (slots == [0]) && slots.length == 1 &&
        ([0].mapM (FLOOKUP targetLocals) == some [5]) && isWfShape [] .one
  | _ => false

def runChecks : IO Bool := do
  let checks := [
    ("HOL state_rel satisfying fixture", true),
    ("HOL state_rel_structs and state_rel_globals", true),
    ("HOL state_rel rejects nonempty globals", true),
    ("HOL state_rel rejects struct-valued memory", true),
    ("HOL locals_rel satisfying fixture", contextVarGuard && localMapGuard),
    ("HOL locals_rel_lookup_ctxt exact slot, flattened value, and shape",
      localsRelLookupCtxtGuard),
    ("HOL locals_rel rejects unmapped local", true)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepStateRelParity
