import Flapjack.CrepeStateRelation

/-!
Generic relation-aware correctness for ordinary Pancake declarations.

compileProg lowers a declaration to a list of Crep declarations.  This file
records the corresponding sequential evaluation obligation once, so the
program correctness induction does not need to duplicate the nested-decision
bookkeeping for every declaration shape.
-/

namespace Flapjack

def CrepDistinctNames : List Nat → Prop
  | [] => True
  | name :: names => name ∉ names ∧ CrepDistinctNames names

theorem restoreCrepResultList_update_of_not_mem
    [OfNat α 0]
    (locals : Nat → Option α) (name : Nat) (value : α)
    (names : List Nat) (result : CrepControlResult α)
    (hnot : name ∉ names) :
    restoreCrepResultList (updateCrepLocal locals name value) names result =
      restoreCrepResultList (updateCrepLocal locals name 0) names result := by
  induction names generalizing locals result with
  | nil => simp [restoreCrepResultList]
  | cons head names ih =>
      have hhead : name ≠ head := by
        intro heq
        apply hnot
        simp [heq]
      have hhead' : head ≠ name := Ne.symm hhead
      have htail : name ∉ names := by
        intro hmem
        apply hnot
        simp [hmem]
      have hcommValue :
          updateCrepLocal (updateCrepLocal locals name value) head 0 =
            updateCrepLocal (updateCrepLocal locals head 0) name value := by
        funext current
        by_cases hcurrentName : current = name <;>
          by_cases hcurrentHead : current = head <;>
          simp [updateCrepLocal, hcurrentName, hcurrentHead, hhead, hhead']
      have hcommZero :
          updateCrepLocal (updateCrepLocal locals name 0) head 0 =
            updateCrepLocal (updateCrepLocal locals head 0) name 0 := by
        funext current
        by_cases hcurrentName : current = name <;>
          by_cases hcurrentHead : current = head <;>
          simp [updateCrepLocal, hcurrentName, hcurrentHead, hhead, hhead']
      simp only [restoreCrepResultList]
      rw [hcommValue]
      rw [ih (locals := updateCrepLocal locals head 0)
        (result := result) htail]
      rw [hcommZero]
      have holdValue :
          updateCrepLocal locals name value head =
            updateCrepLocal locals name 0 head := by
        simp [updateCrepLocal, hhead']
      rw [holdValue]

/-! The recursive witness describes evaluation of the expressions and body
    used by nestedDecs.  Expressions are evaluated in sequence, matching
    the updates made visible by the generated declarations. -/
def CrepNestedDecsEval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) :
    List Nat → List (CrepExp α) → CrepProg α → CrepControlResult α → Prop
  | [], [], body, result =>
      evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress fuel state body = some result
  | name :: names, expression :: expressions, body, result =>
      ∃ value,
        evalCrepFullExp state.locals state.memory
          baseAddress topAddress expression = some value ∧
        CrepNestedDecsEval functions primitive ffi sharedMem
          baseAddress topAddress fuel
          { state with locals := updateCrepLocal state.locals name value }
          names expressions body result
  | _, _, _, _ => False

theorem evalCrepFullProg_nestedDecs_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (names : List Nat)
    (expressions : List (CrepExp α)) (body : CrepProg α)
    (result : CrepControlResult α)
    (hdistinct : CrepDistinctNames names)
    (heval : CrepNestedDecsEval functions primitive ffi sharedMem
      baseAddress topAddress fuel state names expressions body result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names expressions body) =
      some (restoreCrepResultList state.locals names result) := by
  induction names generalizing state expressions with
  | nil =>
      simp [CrepDistinctNames] at hdistinct
      cases expressions with
      | nil =>
          simpa [CrepNestedDecsEval, nestedDecs,
            restoreCrepResultList] using heval
      | cons expression expressions =>
          simp [CrepNestedDecsEval] at heval
  | cons name names ih =>
      rcases hdistinct with ⟨hnotmem, htailDistinct⟩
      cases expressions with
      | nil =>
          simp [CrepNestedDecsEval] at heval
      | cons expression expressions =>
          rcases heval with ⟨value, hvalue, htail⟩
          have htail' := ih
            (state := { state with
              locals := updateCrepLocal state.locals name value })
            (expressions := expressions) htailDistinct htail
          have hrest := restoreCrepResultList_update_of_not_mem
            state.locals name value names result hnotmem
          change evalCrepFullProg functions primitive ffi sharedMem
            baseAddress topAddress (fuel + names.length + 1) state
            (.dec name expression (nestedDecs names expressions body)) = _
          simp only [evalCrepFullProg, hvalue]
          simp [Option.bind]
          rw [htail']
          simp [hrest, restoreCrepResultList, restoreCrepResult]

/-! This is the ordinary-declaration boundary used by the full source
    simulation.  The source expression/body and the sequential Crep binding
    witness are supplied by the expression and recursive-program cases; the
    theorem handles restoration and exposes the control relation. -/
theorem compile_full_pan_value_dec_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (compiledValues : List (CrepExp α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompile : compileExp context value = (compiledValues, shape))
    (hlength : (allocatedNames context shape).length = compiledValues.length)
    (hsourceValue : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord value = some sourceValue)
    (hshape : panShapeMatches (panValueShape structs sourceValue) shape = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceGlobals sourceMemory body = some sourceResult)
    (hcrep : CrepNestedDecsEval functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state (allocatedNames context shape)
      compiledValues
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) crepResult)
    (hdistinct : CrepDistinctNames (allocatedNames context shape))
    (hrel : panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.dec name shape value body) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (fuel + (allocatedNames context shape).length) state
      (compileProg context (.dec name shape value body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  have hcompileProg :
      compileProg context (.dec name shape value body) =
        nestedDecs (allocatedNames context shape) compiledValues
          (compileProg
            { context with
                vars := (name, (shape, allocatedNames context shape)) :: context.vars
                maxVar := context.maxVar + Shape.shapeSize shape }
            body) := by
    simp [compileProg, hcompile, hlength]
  have htarget := evalCrepFullProg_nestedDecs_of_eval
    functions crepPrimitive ffi sharedMem baseAddress topAddress fuel state
      (allocatedNames context shape) compiledValues
    (compileProg
      { context with
          vars := (name, (shape, allocatedNames context shape)) :: context.vars
          maxVar := context.maxVar + Shape.shapeSize shape }
      body) crepResult hdistinct hcrep
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue,
      hshape, hsourceBody, restorePanValueControlLocal]
  constructor
  · exact htarget
  · exact hrel

end Flapjack
