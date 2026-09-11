import Flapjack.CrepeExpressionRelation

/-!
List-level composition for scalar source-word expressions.

This is the expression boundary needed by arbitrary record declarations: each
source field is compiled to one Crep expression, and the resulting list is
evaluated against the flattened word list in source order.
-/

namespace Flapjack

theorem compileSourceWordExpList_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expressions : List (SourceWordExp α)) (values : List α)
    (hsource : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord
      (expressions.map SourceWordExp.toExp) =
      some (values.map (fun value => .word value))) :
    ∃ compiled,
      compileExp.compileExpList context
          (expressions.map SourceWordExp.toExp) =
        compiled.map (fun compiled => ([compiled], .one)) ∧
      evalCrepFullExps crepLocals crepMemory baseAddress topAddress compiled =
        some values ∧
      compiled.length = values.length := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil =>
          exact ⟨[], by simp [compileExp.compileExpList], by
            simp [evalCrepFullExps], by simp⟩
      | cons value values =>
          simp [evalPanValueExp.evalPanValueExps] at hsource
  | cons expression expressions ih =>
      cases values with
      | nil =>
          cases hhead : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord expression.toExp with
          | none =>
              simp [evalPanValueExp.evalPanValueExps, hhead] at hsource
          | some sourceValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (expressions.map SourceWordExp.toExp) with
              | none =>
                  simp [evalPanValueExp.evalPanValueExps, hhead, htail] at hsource
              | some sourceValues =>
                  simp [evalPanValueExp.evalPanValueExps, hhead, htail] at hsource
      | cons value values =>
          cases hhead : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord expression.toExp with
          | none =>
              simp [evalPanValueExp.evalPanValueExps, hhead] at hsource
          | some sourceValue =>
              cases htail : evalPanValueExp.evalPanValueExps structs sourceLocals
                  sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                  (expressions.map SourceWordExp.toExp) with
              | none =>
                  simp [evalPanValueExp.evalPanValueExps, hhead, htail] at hsource
              | some sourceValues =>
                  have hsourceEq :
                      some (sourceValue :: sourceValues) =
                        some (.word value :: values.map (fun value => .word value)) := by
                    simpa [evalPanValueExp.evalPanValueExps, hhead, htail] using hsource
                  have hsourceEq' := Option.some.inj hsourceEq
                  have hsourceValue : sourceValue = .word value := by
                    injection hsourceEq'
                  have hsourceValues :
                      sourceValues = values.map (fun value => .word value) := by
                    injection hsourceEq'
                  cases hsourceValue
                  cases hsourceValues
                  have hheadSource :
                      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                        baseAddress topAddress bytesInWord expression.toExp =
                        some (.word value) := by
                    rw [hhead]
                  have htailSource :
                      evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
                        sourceMemory baseAddress topAddress bytesInWord
                        (expressions.map SourceWordExp.toExp) =
                        some (values.map (fun value => .word value)) := by
                    rw [htail]
                  obtain ⟨head, hheadCompile, hheadEval⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory crepLocals crepMemory
                      baseAddress topAddress bytesInWord hbytesInWord hlocals
                      hlookup expression value hheadSource
                  obtain ⟨tail, htailCompile, htailEval, htailLength⟩ :=
                    ih values htailSource
                  refine ⟨head :: tail, ?_, ?_, ?_⟩
                  · simp [compileExp.compileExpList, hheadCompile, htailCompile]
                  · simp [evalCrepFullExps, hheadEval, htailEval]
                  · simp [htailLength]

theorem compileSourceWordExp_rStruct_list_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expressions : List (SourceWordExp α)) (values : List α)
    (hsource : evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord
      (expressions.map SourceWordExp.toExp) =
      some (values.map (fun value => .word value))) :
    ∃ compiled,
      compileExp context (.rStruct (expressions.map SourceWordExp.toExp)) =
        (compiled, .comb (values.map (fun _ => .one))) ∧
      evalCrepFullExps crepLocals crepMemory baseAddress topAddress compiled =
        some values := by
  obtain ⟨compiled, hcompileList, hcompiled, hlength⟩ :=
    compileSourceWordExpList_relation context structs sourceLocals sourceGlobals
      sourceMemory crepLocals crepMemory baseAddress topAddress bytesInWord
      hbytesInWord hlocals hlookup expressions values hsource
  refine ⟨compiled, ?_, hcompiled⟩
  have hflatAux : ∀ xs : List (CrepExp α),
      List.flatMap Prod.fst (xs.map (fun compiled => ([compiled], Shape.one))) = xs := by
    intro xs
    induction xs with
    | nil => simp
    | cons head tail ih =>
        simpa only [List.map_cons, List.flatMap_cons, List.singleton_append,
          List.nil_append] using congrArg (fun ys => head :: ys) ih
  have hshapeAux : ∀ (xs : List (CrepExp α)) (ys : List α),
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
  have hflat := hflatAux compiled
  have hshape := hshapeAux compiled values hlength
  simp only [compileExp]
  rw [hcompileList]
  rw [hflat, hshape]

end Flapjack
