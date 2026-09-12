import Flapjack.CrepeSourceWordLoadCorrectness
import Flapjack.CrepeReturnCorrectness
import Flapjack.CrepeProgramReturnFuelRelation

/-!
Package a one-word source load into the full source-to-Crep return boundary.
The expression-level load theorem supplies the compiler and memory witnesses;
the existing return theorem supplies control-result and payload handling.
-/

namespace Flapjack

theorem compile_full_pan_value_return_load_one_relation
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
    (address : SourceWordExp α) (addressValue value : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceAddress : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord address.toExp = some (.word addressValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.load .one address.toExp) =
      some (.word value)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 1 sourceLocals sourceGlobals sourceMemory
      (.return (.load .one address.toExp)) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [.word value]) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress 1 state
      (compileProg context (.return (.load .one address.toExp))) =
      some (.returned state [value]) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [.word value])
      (.returned state [value]) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWord_load_one_state_relation
    context structs sourceLocals sourceGlobals sourceMemory state baseAddress
    topAddress bytesInWord address addressValue value hbytesInWord hlocals hlookup
    hsourceAddress hsource
  have hcompileShape : compileExp context (.load .one address.toExp) =
      ([compiled], panValueShape structs (.word value)) := by
    simpa [panValueShape] using hcompile
  have hcompiledList : evalCrepFullExpsState state
      baseAddress topAddress [compiled] =
      some (panValueFlatWords (.word value)) := by
    simp [evalCrepFullExpsState, hcompiled, panValueFlatWords,
      panValueFlatWordsFuel]
  exact compile_full_pan_value_return_state_relation_fuel context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    0 0 (.load .one address.toExp) (.word value) [compiled] exceptionRel hsource
    (by simp) hcompileShape hcompiledList hlocals

end Flapjack
