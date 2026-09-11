import Flapjack.CrepeCallDestinationReadback
import Flapjack.CrepeStateRelationExtension

/-!
Normal destination-aware calls provide the state relation needed by a
declaration-call continuation.  This packages call evaluation, destination
read-back, and arbitrary-shape relation extension into one reusable theorem.
-/

namespace Flapjack

theorem evalCrepFullCall_returned_state_extension
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceLocals' sourceGlobals :
      VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (caller : CrepState α) (function : FunName)
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (destinations : List Nat) (arguments : List (CrepExp α))
    (values : List α) (parameters : List Nat) (body : CrepProg α)
    (calleeLocals : Nat → Option α) (callee : CrepState α)
    (calleeValues : List α) (callerLocals : Nat → Option α)
    (name : VarName) (shape : Shape) (value : PanValue α)
    (hcalleeValues : calleeValues = panValueFlatWords value)
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments = some values)
    (hlookup : lookupCompiledFunction function functions =
      some (parameters, body))
    (hassign : assignCrepValues (fun _ => none) parameters values =
      some calleeLocals)
    (hcallee : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := calleeLocals, memory := caller.memory } body =
      some (.returned callee calleeValues))
    (hdestinations : assignCrepValues caller.locals destinations calleeValues =
      some callerLocals)
    (hdistinct : CrepDistinctNames destinations)
    (hsource : sourceLocals' = updatePanValueMap sourceLocals name value)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hname : lookupInfo name context.vars = none)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ destination, destination ∈ destinations → destination ∉ oldSlots)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory caller)
    (hmemory : panValueCrepMemoryRel sourceMemory callee.memory) :
    evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (some (destinations, none)) function arguments =
      some (.normal { locals := callerLocals, memory := callee.memory }) ∧
    panValueCrepStateRel structs
      { context with vars := (name, (shape, destinations)) :: context.vars }
      sourceLocals' sourceGlobals sourceMemory
      { locals := callerLocals, memory := callee.memory } := by
  have hcall := evalCrepFullCall_returned_destinations_read_back
    functions primitive ffi sharedMem baseAddress topAddress fuel caller function
    destinations arguments values parameters body calleeLocals callee calleeValues
    callerLocals hvalues hlookup hassign hcallee hdestinations hdistinct
  have hread : readCrepLocals callerLocals destinations =
      some (panValueFlatWords value) := by
    simpa [hcalleeValues] using hcall.2
  have hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals callerLocals oldSlots =
        some (panValueFlatWords oldValue) := by
    intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
    have holdOld := hrel.2.1 oldName oldValue oldShape oldSlots
      hsourceOld hlookupOld
    have hpreserve := assignCrepValues_read_preserve caller.locals
      destinations calleeValues callerLocals oldSlots hdestinations
      (fun destination hdestination =>
        hnoalias oldName oldShape oldSlots hne hlookupOld destination
          hdestination)
    exact ⟨holdOld.1, hpreserve.symm ▸ holdOld.2⟩
  have hlocals : panValueCrepLocalsRel structs context sourceLocals callerLocals := by
    intro current currentValue currentShape currentSlots hcurrent hlookup
    have hcurrentName : current ≠ name := by
      intro heq
      subst current
      rw [hname] at hlookup
      cases hlookup
    exact hold current currentValue currentShape currentSlots hcurrentName
      hcurrent hlookup
  have hrel' : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory { locals := callerLocals, memory := callee.memory } :=
    ⟨hrel.1, hlocals, hmemory⟩
  have hstate := panValueCrepStateRel_extend
    structs context sourceLocals sourceLocals' sourceGlobals sourceMemory
    { locals := callerLocals, memory := callee.memory }
    name shape destinations value hsource hshape hread hold hrel'
  exact ⟨hcall.1, hstate⟩

end Flapjack
