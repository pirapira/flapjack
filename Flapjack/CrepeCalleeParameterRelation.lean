import Flapjack.CrepeLocalsRelationUpdateGeneral
import Flapjack.CrepeStateRelationExtension

/-!
Fresh callee-parameter transport for arbitrary flattened Pancake values.

The source callee receives one structured value, while Crep receives its
flattened words in the slots assigned by the compiler.  Updating those slots
first makes the old local relation available to the generic context-extension
rule, and the explicit freshness premise prevents the new words from changing
any pre-existing binding.
-/

namespace Flapjack

theorem panValueCrepStateRel_add_parameter_fresh
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α) (values : List α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hname : lookupInfo name context.vars = none)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hflat : panValueFlatWords value = values)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    panValueCrepStateRel structs
      { context with vars := (name, (shape, slots)) :: context.vars }
      (updatePanValueMap sourceLocals name value) sourceGlobals sourceMemory
      { state with
          locals := updateCrepLocalList state.locals slots values } := by
  have hupdated : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory
      { state with locals := updateCrepLocalList state.locals slots values } := by
    refine ⟨hrel.1, ?_, hrel.2.2⟩
    intro oldName oldValue oldShape oldSlots hsourceOld hlookupOld
    have hold := hrel.2.1 oldName oldValue oldShape oldSlots hsourceOld hlookupOld
    have hnameNe : oldName ≠ name := by
      intro heq
      subst oldName
      rw [hname] at hlookupOld
      cases hlookupOld
    have hnot : ∀ slot ∈ slots, slot ∉ oldSlots :=
      hnoalias oldName oldShape oldSlots hnameNe hlookupOld
    have hread := readCrepLocals_updateCrepLocalList_of_not_mem
      state.locals slots values oldSlots hlength hnot
    exact ⟨hold.1, hread.symm ▸ hold.2⟩
  have hread : readCrepLocals
      (updateCrepLocalList state.locals slots values) slots =
      some (panValueFlatWords value) := by
    have hread' := readCrepLocals_updateCrepLocalList state.locals slots values
      hlength hdistinct
    simpa [hflat] using hread'
  have hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals (updateCrepLocalList state.locals slots values) oldSlots =
        some (panValueFlatWords oldValue) := by
    intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
    exact hupdated.2.1 oldName oldValue oldShape oldSlots hsourceOld hlookupOld
  exact panValueCrepStateRel_extend structs context sourceLocals
    (updatePanValueMap sourceLocals name value) sourceGlobals sourceMemory
    { state with locals := updateCrepLocalList state.locals slots values }
    name shape slots value rfl hshape hread hold hupdated

theorem panValueCrepCalleeStateRel_parameter_fresh
    [OfNat α 0]
    [LawfulBEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (name : VarName) (shape : Shape) (slots : List Nat)
    (value : PanValue α) (values : List α)
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hname : lookupInfo name context.vars = none)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hlength : slots.length = values.length)
    (hdistinct : CrepDistinctNames slots)
    (hflat : panValueFlatWords value = values)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ slots, slot ∉ oldSlots) :
    panValueCrepStateRel structs
      { context with vars := (name, (shape, slots)) :: context.vars }
      (updatePanValueMap (fun _ => none) name value) sourceGlobals sourceMemory
      { locals := updateCrepLocalList (fun _ => none) slots values,
        memory := crepMemory } := by
  have hrel : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { locals := (fun _ => none), memory := crepMemory } := by
    refine ⟨hglobals, panValueCrepLocalsRel_empty structs context (fun _ => none), ?_⟩
    exact hmemory
  exact panValueCrepStateRel_add_parameter_fresh structs context
    (fun _ => none) sourceGlobals sourceMemory
    { locals := (fun _ => none), memory := crepMemory }
    name shape slots value values hrel hname hshape hlength hdistinct hflat hnoalias

end Flapjack
