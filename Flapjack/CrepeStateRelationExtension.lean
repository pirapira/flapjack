import Flapjack.CrepeStateRelation

/-!
State-relation extension for an arbitrary flattened Pancake value.

The source environment gains one structured binding while the Crep state
receives the words for that value in the supplied slots.  The generic local
relation already contains the lookup and non-aliasing argument; this wrapper
keeps globals and memory unchanged and gives declaration/call correctness a
single state-level interface.
-/

namespace Flapjack

theorem panValueCrepStateRel_extend
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceLocals' sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α)
    (hsource : sourceLocals' = updatePanValueMap sourceLocals name value)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hread : readCrepLocals state.locals slots =
      some (panValueFlatWords value))
    (hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals state.locals oldSlots =
        some (panValueFlatWords oldValue))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    panValueCrepStateRel structs
      { context with
          vars := (name, (shape, slots)) :: context.vars }
      sourceLocals' sourceGlobals sourceMemory state := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  exact panValueCrepLocalsRel_extend structs context sourceLocals sourceLocals'
    state.locals name shape slots value hsource hshape hread hold

end Flapjack

namespace Flapjack

theorem readCrepLocals_initialize_of_not_mem
    [OfNat α 0]
    (locals : Nat → Option α) (names slots : List Nat)
    (hnot : ∀ name, name ∈ names → name ∉ slots) :
    readCrepLocals (initializeCrepLocals locals names) slots =
      readCrepLocals locals slots := by
  induction names generalizing locals with
  | nil =>
      rfl
  | cons name names ih =>
      have htail : ∀ current, current ∈ names → current ∉ slots := by
        intro current hcurrent
        exact hnot current (by simp [hcurrent])
      have hhead : name ∉ slots := hnot name (by simp)
      simp only [initializeCrepLocals]
      rw [ih (locals := updateCrepLocal locals name 0) htail]
      exact readCrepLocals_update_of_not_mem locals name 0 slots hhead

theorem initializeCrepLocals_defined
    [OfNat α 0]
    (locals : Nat → Option α) (names : List Nat) :
    ∀ name, name ∈ names →
      (initializeCrepLocals locals names name).isSome = true := by
  have hpreserve : ∀ (base : Nat → Option α) (names : List Nat) (name : Nat),
      (base name).isSome = true →
      (initializeCrepLocals base names name).isSome = true := by
    intro base names name hbase
    induction names generalizing base with
    | nil =>
        simpa [initializeCrepLocals] using hbase
    | cons head names ih =>
        simp only [initializeCrepLocals]
        by_cases heq : name = head
        · apply ih
          simp [updateCrepLocal, heq]
        · apply ih (base := updateCrepLocal base head 0)
          simpa [updateCrepLocal, heq] using hbase
  induction names generalizing locals with
  | nil =>
      simp
  | cons head names ih =>
      intro name hname
      have htail : ∀ current, current ∈ names →
          (initializeCrepLocals (updateCrepLocal locals head 0) names current).isSome = true := by
        intro current hcurrent
        exact ih (locals := updateCrepLocal locals head 0) current hcurrent
      rcases (by simpa [List.mem_cons] using hname) with heq | hcurrent
      · exact hpreserve (updateCrepLocal locals head 0) names name
          (by simp [heq, updateCrepLocal])
      · simp only [initializeCrepLocals]
        exact htail name hcurrent

theorem panValueCrepStateRel_initialize
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (slots : List Nat)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hname : lookupInfo name context.vars = none)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ slots → temporary ∉ oldSlots) :
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory { state with locals := initializeCrepLocals state.locals slots } := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro oldName oldValue oldShape oldSlots hsourceOld hlookupOld
  have hold := hrel.2.1 oldName oldValue oldShape oldSlots hsourceOld hlookupOld
  have hnameNe : oldName ≠ name := by
    intro heq
    subst oldName
    rw [hname] at hlookupOld
    cases hlookupOld
  have hnot : ∀ temporary, temporary ∈ slots → temporary ∉ oldSlots :=
    hnoalias oldName oldShape oldSlots hnameNe hlookupOld
  exact ⟨hold.1,
    (readCrepLocals_initialize_of_not_mem state.locals slots oldSlots hnot).symm ▸
      hold.2⟩

end Flapjack

namespace Flapjack

/-! The corresponding extension rule when a callee has also produced a new
    source global environment and memory relation.  The local proof still
    uses the caller relation for pre-existing bindings, while the global and
    memory components come from the callee simulation. -/
theorem panValueCrepStateRel_extend_environment
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceLocals' : VarName → Option (PanValue α))
    (sourceGlobals' : VarName → Option (PanValue α))
    (sourceMemory' : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α)
    (hsource : sourceLocals' = updatePanValueMap sourceLocals name value)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hread : readCrepLocals state.locals slots =
      some (panValueFlatWords value))
    (hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals state.locals oldSlots =
        some (panValueFlatWords oldValue))
    (hglobals : sourceGlobals' = (fun _ => none))
    (hmemory : panValueCrepMemoryRel sourceMemory' state.memory) :
    panValueCrepStateRel structs
      { context with
          vars := (name, (shape, slots)) :: context.vars }
      sourceLocals' sourceGlobals' sourceMemory' state := by
  have hlocals := panValueCrepLocalsRel_extend structs context sourceLocals
    sourceLocals' state.locals name shape slots value hsource hshape hread hold
  exact ⟨hglobals, hlocals, hmemory⟩

end Flapjack
