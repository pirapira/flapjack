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
