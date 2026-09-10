import Flapjack.CrepeStateRelation

/-!
Expression correctness at the source-to-Crep boundary.

These base cases connect the state relation to the actual `compileExp`
output.  They are intentionally separate from the larger program theorem so
that the expression induction can grow without making the state-relation file
depend on statement lowering.
-/

namespace Flapjack

theorem compileExp_const_word_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord value : α) :
    compileExp context (.const value) = ([.const value], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.const value) = some (.word value) ∧
    evalCrepFullExps crepLocals crepMemory baseAddress topAddress
      [.const value] = some [value] := by
  simp [compileExp, evalPanValueExp, evalCrepFullExps, evalCrepFullExp]

theorem compileExp_local_word_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (name : VarName) (slot : Nat) (value : α)
    (hlookup : lookupInfo name context.vars = some (.one, [slot]))
    (hsource : sourceLocals name = some (.word value))
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals) :
    compileExp context (.var .local name) = ([.var slot], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) = some (.word value) ∧
    evalCrepFullExps crepLocals crepMemory baseAddress topAddress
      [.var slot] = some [value] := by
  have hlocal := hrel name (.word value) .one [slot] hsource hlookup
  have hslot : crepLocals slot = some value := by
    cases h : crepLocals slot with
    | none => simp [readCrepLocals, h] at hlocal
    | some currentValue =>
        have hvalue : currentValue = value := by
          simpa [readCrepLocals, h, panValueFlatWords,
            panValueFlatWordsFuel, panValueFlatValueFuel] using hlocal.2
        simp [hvalue]
  simp [compileExp, hlookup, evalPanValueExp, hsource,
    evalCrepFullExps, evalCrepFullExp, hslot]

theorem compileExp_rStruct_const_words_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α) (values : List α) :
    compileExp context (.rStruct (values.map (fun value => .const value))) =
      (values.map (fun value => .const value),
        .comb (values.map (fun _ => .one))) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct (values.map (fun value => .const value))) =
      some (.rStruct (values.map (fun value => .word value))) ∧
    evalCrepFullExps crepLocals crepMemory baseAddress topAddress
      (values.map (fun value => .const value)) = some values := by
  have hcompileList :
      compileExp.compileExpList context
          (values.map (fun value => .const value)) =
        values.map (fun value => ([.const value], .one)) := by
    induction values with
    | nil => simp [compileExp.compileExpList]
    | cons value values ih =>
        simp [compileExp.compileExpList, compileExp, ih]
  have hsourceList :
      evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord
          (values.map (fun value => .const value)) =
        some (values.map (fun value => .word value)) := by
    clear hcompileList
    induction values with
    | nil => simp [evalPanValueExp.evalPanValueExps]
    | cons value values ih =>
        simp [evalPanValueExp.evalPanValueExps, evalPanValueExp, ih]
  have hcrepList :
      evalCrepFullExps crepLocals crepMemory baseAddress topAddress
          (values.map (fun value => .const value)) = some values := by
    clear hcompileList hsourceList
    induction values with
    | nil => simp [evalCrepFullExps]
    | cons value values ih =>
        simp [evalCrepFullExps, evalCrepFullExp, ih]
  have hflat :
      List.flatMap Prod.fst
          (values.map (fun value => ([CrepExp.const value], Shape.one))) =
        values.map (fun value => CrepExp.const value) := by
    clear hcompileList hsourceList hcrepList
    induction values with
    | nil => simp
    | cons value values ih => simp [ih]
  simp [compileExp, evalPanValueExp, hcompileList, hsourceList, hcrepList,
    hflat]

end Flapjack
