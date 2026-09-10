import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeAssignmentCorrectness

/-!
The source-word expression relation also gives a state-threaded local
assignment rule.  The direct assignment branch is isolated here; the
temporary branch for expressions that mention their destination follows once
the fresh-slot relation is connected to the expression theorem.
-/

namespace Flapjack

theorem compile_full_pan_value_local_assign_source_word_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slot : Nat) (oldValue value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hold : sourceLocals name = some (.word oldValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExp state.locals state.memory baseAddress topAddress
      compiled = some value)
    (hdistinct : distinctLists [slot] (crepExpVars compiled))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hnoalias : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      slot ∉ oldSlots) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 1
      sourceLocals sourceGlobals sourceMemory
      (.assign .local name expression.toExp) =
      some (.normal (updatePanValueMap sourceLocals name (.word value))
        sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 2 state
      (compileProg context (.assign .local name expression.toExp)) =
      some (.normal { state with locals := updateCrepLocal state.locals slot value }) ∧
    panValueCrepStateRel structs context
      (updatePanValueMap sourceLocals name (.word value)) sourceGlobals sourceMemory
      { state with locals := updateCrepLocal state.locals slot value } := by
  have hcompileProg : compileProg context (.assign .local name expression.toExp) =
      .seq (.assign slot compiled) .skip := by
    simp [compileProg, hlookup, hcompile, hdistinct, crepNestedSeq]
  rw [hcompileProg]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hold,
      panValueAssignmentValid, panValueShape, panShapeMatches]
  constructor
  · simp [evalCrepFullProg, hcompiled]
  · refine ⟨hrel.1, ?_, hrel.2.2⟩
    exact panValueCrepLocalsRel_update_word structs context sourceLocals
      state.locals name slot value hrel.2.1 hlookup hnoalias

end Flapjack
