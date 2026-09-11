import Flapjack.CrepeStateRelationExtension
import Flapjack.CrepeProgramRelation
import Flapjack.CrepeAssignmentReadback

/-!
State extension for a recursively correct returned callee.

The recursive body theorem relates the source callee state and returned
values to the target callee.  This theorem performs the destination
assignment and extends the caller relation while retaining the globals and
memory produced by the callee.
-/

namespace Flapjack

theorem evalCrepFullCall_returned_state_extension_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (caller : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (name : VarName) (shape : Shape) (function : FunName)
    (calleeContext : CompileContext α)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceBodyLocals : VarName → Option (PanValue α))
    (sourceValues : List (PanValue α))
    (argumentValues targetValues : List α)
    (parameters : List Nat) (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (targetCallerLocals : Nat → Option α)
    (value : PanValue α)
    (hbody : PanValueCrepProgramCorrect sourceBody)
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hrelCallee : panValueCrepStateRel structs
      calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := caller.memory })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceMemory sourceBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.returned targetCallee targetValues))
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions = some (parameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) parameters argumentValues =
      some targetCalleeLocals)
    (hdestinations : assignCrepValues caller.locals (allocatedNames context shape)
      targetValues = some targetCallerLocals)
    (hcalleeValues : targetValues = panValueFlatWords value)
    (hshape : panShapeMatches (panValueShape structs value) shape = true)
    (hdistinct : CrepDistinctNames (allocatedNames context shape))
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ destination, destination ∈ allocatedNames context shape →
        destination ∉ oldSlots)
    (hcallerRel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory caller) :
    evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal { locals := targetCallerLocals, memory := targetCallee.memory }) ∧
    panValueCrepStateRel structs
      { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      (updatePanValueMap sourceLocals name value) sourceCalleeGlobals
      sourceCalleeMemory
      { locals := targetCallerLocals, memory := targetCallee.memory } := by
  have hcrepBody' : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory }
      (compileProg calleeContext sourceBody) = some (.returned targetCallee targetValues) := by
    rw [hcompileBody]
    exact hcrepBody
  have hbodyRel := hbody calleeContext
    structs sourceFunctions functions sourceCalleeLocals sourceGlobals
    sourceMemory { locals := targetCalleeLocals, memory := caller.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceValues)
    (.returned targetCallee targetValues) hrelCallee hsourceBody hcrepBody'
  have hbodyStateRel : panValueCrepStateRel structs
      calleeContext
      sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory targetCallee :=
    hbodyRel.1
  have hread : readCrepLocals targetCallerLocals
      (allocatedNames context shape) = some targetValues :=
    assignCrepValues_read_back caller.locals (allocatedNames context shape)
      targetValues targetCallerLocals hdestinations hdistinct
  have hold : ∀ oldName oldValue oldShape oldSlots,
      oldName ≠ name →
      sourceLocals oldName = some oldValue →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      panShapeMatches (panValueShape structs oldValue) oldShape = true ∧
      readCrepLocals targetCallerLocals oldSlots =
        some (panValueFlatWords oldValue) := by
    intro oldName oldValue oldShape oldSlots hne hsourceOld hlookupOld
    have holdOld := hcallerRel.2.1 oldName oldValue oldShape oldSlots
      hsourceOld hlookupOld
    have hpreserve := assignCrepValues_read_preserve caller.locals
      (allocatedNames context shape) targetValues targetCallerLocals oldSlots
      hdestinations (fun destination hdestination =>
        hnoalias oldName oldShape oldSlots hne hlookupOld destination hdestination)
    exact ⟨holdOld.1, hpreserve.symm ▸ holdOld.2⟩
  have hcall := evalCrepFullCall_returned_with_destinations
    functions crepPrimitive ffi sharedMem baseAddress topAddress targetFuel caller
    function (allocatedNames context shape) compiledArguments argumentValues parameters
    targetBody targetCalleeLocals targetCallee targetValues targetCallerLocals
    hvalues hlookup hassign hcrepBody hdestinations
  have hstate := panValueCrepStateRel_extend_environment
    structs context sourceLocals
    (updatePanValueMap sourceLocals name value) sourceCalleeGlobals
    sourceCalleeMemory { locals := targetCallerLocals, memory := targetCallee.memory }
    name shape (allocatedNames context shape) value rfl hshape
    (by simpa [hcalleeValues] using hread) hold
    hbodyStateRel.1 hbodyStateRel.2.2
  change panValueCrepStateRel structs
      { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      (updatePanValueMap sourceLocals name value) sourceCalleeGlobals sourceCalleeMemory
      { locals := targetCallerLocals, memory := targetCallee.memory } at hstate
  exact ⟨hcall, hstate⟩

end Flapjack
