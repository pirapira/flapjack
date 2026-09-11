import Flapjack.CrepeExpressionListRelation

/-!
Source-side inversion for structured scalar records.  Successful evaluation
of a record expression made from scalar word expressions produces a record of
words, with the same list-level evaluator result.  This is the source-value
inversion needed before applying the generic assignment correctness rules.
-/

namespace Flapjack

theorem evalPanValueExp_sourceWordRecord_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (context : CompileContext α)
    (crepLocals : Nat → Option α)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (fields : List (SourceWordExp α)) (sourceValue : PanValue α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (fields.map SourceWordExp.toExp)) = some sourceValue) :
    ∃ values : List α,
      sourceValue = .rStruct (values.map (fun value => .word value)) ∧
      evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (fields.map SourceWordExp.toExp) =
        some (values.map (fun value => .word value)) := by
  cases hvalues : evalPanValueExp.evalPanValueExps structs sourceLocals
      sourceGlobals sourceMemory baseAddress topAddress bytesInWord
      (fields.map SourceWordExp.toExp) with
  | none =>
      simp [evalPanValueExp, hvalues] at hsource
  | some values =>
      have hrecord : .rStruct values = sourceValue := by
        exact Option.some.inj (by simpa [evalPanValueExp, hvalues] using hsource)
      obtain ⟨words, hwords, hlength⟩ := evalSourceWordExpList_inv
        structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
        bytesInWord context crepLocals hlocals hlookup fields values hvalues
      refine ⟨words, ?_, ?_⟩
      · simpa [hwords] using hrecord.symm
      · rw [← hwords]

end Flapjack
