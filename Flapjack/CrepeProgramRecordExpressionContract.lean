import Flapjack.CrepeExpressionListRelation
import Flapjack.CrepeSourceWordRecordExpressionInversion

/-!
An executable expression contract for anonymous records of scalar word
expressions.  It packages source record inversion together with the compiled
flat-expression list, its target evaluation, and the length equation required
by both structured assignment lowerings.
-/

namespace Flapjack

theorem panValueCrepRecordExpressionContract_sourceWord
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (fields : List (SourceWordExp α))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
      (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory state →
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue →
      ∃ values compiled,
        sourceValue = .rStruct (values.map (fun value => .word value)) ∧
        compileExp context (.rStruct (fields.map SourceWordExp.toExp)) =
          (compiled, .comb (values.map (fun _ => .one))) ∧
        compiled.length = values.length ∧
        evalCrepFullExps state.locals state.memory baseAddress topAddress
          compiled = some values := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨values, hrecordValue, hsourceValues⟩ :=
    evalPanValueExp_sourceWordRecord_inv structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord context state.locals
      hrel.2.1
      (fun name value hvalue => hlookup context sourceLocals name value hvalue)
      fields sourceValue hsource
  obtain ⟨compiled, hcompileList, hcompiled, hcompiledLength⟩ :=
    compileSourceWordExpList_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      (hbytesInWord context bytesInWord) hrel.2.1
      (fun name value hvalue => hlookup context sourceLocals name value hvalue)
      fields values hsourceValues
  refine ⟨values, compiled, hrecordValue, ?_, hcompiledLength, hcompiled⟩
  have hflat : ∀ xs : List (CrepExp α),
      List.flatMap Prod.fst
        (xs.map (fun compiled => ([compiled], Shape.one))) = xs := by
    intro xs
    induction xs with
    | nil => simp
    | cons head tail ih =>
        simpa only [List.map_cons, List.flatMap_cons, List.singleton_append,
          List.nil_append] using congrArg (fun ys => head :: ys) ih
  have hshape : ∀ (xs : List (CrepExp α)) (ys : List α),
      xs.length = ys.length →
      (xs.map (fun compiled => ([compiled], Shape.one))).map Prod.snd =
        ys.map (fun _ => Shape.one) := by
    intro xs
    induction xs with
    | nil =>
        intro ys hlength
        cases ys with
        | nil => rfl
        | cons value values => simp at hlength
    | cons head tail ih =>
        intro ys hlength
        cases ys with
        | nil => simp at hlength
        | cons value values =>
            simp only [List.map_cons]
            congr 1
            exact ih values (by simpa using hlength)
  simp only [compileExp]
  rw [hcompileList, hflat compiled, hshape compiled values hcompiledLength]

end Flapjack
