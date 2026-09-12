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

theorem compileExp_binop_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (operator : BinOp) (left right : α) :
    compileExp context (.op operator [.const left, .const right]) =
      ([.op operator [.const left, .const right]], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.op operator [.const left, .const right]) =
      some (.word (evalPanBinOp operator left right)) ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      (.op operator [.const left, .const right]) =
      some (evalPanBinOp operator left right) := by
  simp [compileExp, compileExp.compileExpList, cexpHeads,
    evalPanValueExp, evalPanValueExp.evalPanValueExps,
    evalCrepFullExp]

theorem compileExp_binop_local_words_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (operator : BinOp)
    (leftName rightName : VarName) (leftSlot rightSlot : Nat)
    (leftValue rightValue : α)
    (hleftLookup : lookupInfo leftName context.vars = some (.one, [leftSlot]))
    (hrightLookup : lookupInfo rightName context.vars = some (.one, [rightSlot]))
    (hleftSource : sourceLocals leftName = some (.word leftValue))
    (hrightSource : sourceLocals rightName = some (.word rightValue))
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals) :
    compileExp context
        (.op operator [.var .local leftName, .var .local rightName]) =
      ([.op operator [.var leftSlot, .var rightSlot]], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (.op operator [.var .local leftName, .var .local rightName]) =
      some (.word (evalPanBinOp operator leftValue rightValue)) ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
        (.op operator [.var leftSlot, .var rightSlot]) =
      some (evalPanBinOp operator leftValue rightValue) := by
  have hleft := hrel leftName (.word leftValue) .one [leftSlot]
    hleftSource hleftLookup
  have hright := hrel rightName (.word rightValue) .one [rightSlot]
    hrightSource hrightLookup
  have hleftSlot : crepLocals leftSlot = some leftValue := by
    cases h : crepLocals leftSlot with
    | none => simp [readCrepLocals, h] at hleft
    | some currentValue =>
        have hvalue : currentValue = leftValue := by
          simpa [readCrepLocals, h, panValueFlatWords,
            panValueFlatWordsFuel, panValueFlatValueFuel] using hleft.2
        simp [hvalue]
  have hrightSlot : crepLocals rightSlot = some rightValue := by
    cases h : crepLocals rightSlot with
    | none => simp [readCrepLocals, h] at hright
    | some currentValue =>
        have hvalue : currentValue = rightValue := by
          simpa [readCrepLocals, h, panValueFlatWords,
            panValueFlatWordsFuel, panValueFlatValueFuel] using hright.2
        simp [hvalue]
  simp [compileExp, compileExp.compileExpList, cexpHeads,
    hleftLookup, hrightLookup, evalPanValueExp,
    evalPanValueExp.evalPanValueExps, hleftSource, hrightSource,
    evalCrepFullExp, hleftSlot, hrightSlot]

theorem compile_full_pan_value_return_local_binop_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (state : CrepState α) (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (operator : BinOp)
    (leftName rightName : VarName) (leftSlot rightSlot : Nat)
    (leftValue rightValue : α)
    (hleftLookup : lookupInfo leftName context.vars = some (.one, [leftSlot]))
    (hrightLookup : lookupInfo rightName context.vars = some (.one, [rightSlot]))
    (hleftSource : sourceLocals leftName = some (.word leftValue))
    (hrightSource : sourceLocals rightName = some (.word rightValue))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      (fun address => (state.memory address).map PanValue.word) state) :
    evalCrepFullResultState [] primitive ffi sharedMem baseAddress topAddress 1 state
        (compileProg context
          (.return (.op operator
            [.var .local leftName, .var .local rightName]))) =
      (evalPanValueProg structs baseAddress topAddress bytesInWord
        sourceLocals sourceGlobals (fun address =>
          (state.memory address).map PanValue.word)
        (.return (.op operator
          [.var .local leftName, .var .local rightName]))).map
        (fun result => result.2.2.2.flatMap panValueFlatWords) := by
  have hexp := compileExp_binop_local_words_correct context structs
    sourceLocals sourceGlobals
    (fun address => (state.memory address).map PanValue.word)
    state.locals state.memory baseAddress topAddress bytesInWord operator
    leftName rightName leftSlot rightSlot leftValue rightValue
    hleftLookup hrightLookup hleftSource hrightSource hrel.2.1
  have hnoGlobal : CrepExpNoGlobal (α := α)
      (CrepExp.op (α := α) operator
        [CrepExp.var (α := α) leftSlot, CrepExp.var (α := α) rightSlot]) :=
    CrepExpNoGlobal.op (operator := operator)
      (left := CrepExp.var (α := α) leftSlot)
      (right := CrepExp.var (α := α) rightSlot)
      (CrepExpNoGlobal.var (α := α) leftSlot)
      (CrepExpNoGlobal.var (α := α) rightSlot)
  have hcompiledState :
      evalCrepFullExpState state baseAddress topAddress
        (CrepExp.op operator [CrepExp.var leftSlot, CrepExp.var rightSlot]) =
      some (evalPanBinOp operator leftValue rightValue) := by
    rw [evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
      (CrepExp.op operator [CrepExp.var leftSlot, CrepExp.var rightSlot])
      hnoGlobal]
    exact hexp.2.2
  exact compile_full_pan_value_return_word_of_exp context structs
    sourceLocals sourceGlobals state primitive ffi sharedMem
    baseAddress topAddress bytesInWord (evalPanBinOp operator leftValue rightValue)
    (.op operator [.var .local leftName, .var .local rightName])
    (CrepExp.op operator [CrepExp.var leftSlot, CrepExp.var rightSlot])
    hexp.2.1 hexp.1 hcompiledState

theorem compileExp_cmp_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (operator : Cmp) (left right : α) :
    compileExp context (.cmp operator (.const left) (.const right)) =
      ([.cmp operator (.const left) (.const right)], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.cmp operator (.const left) (.const right)) =
      some (.word (evalPanCmp operator left right)) ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      (.cmp operator (.const left) (.const right)) =
      some (evalPanCmp operator left right) := by
  simp [compileExp, evalPanValueExp, evalCrepFullExp]

theorem compileExp_shift_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (operator : Shift) (left right : α) :
    compileExp context (.shift operator (.const left) (.const right)) =
      ([.shift operator (.const left) (.const right)], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.shift operator (.const left) (.const right)) =
      (evalPanShift operator left right).map PanValue.word ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      (.shift operator (.const left) (.const right)) =
      evalPanShift operator left right := by
  simp [compileExp, evalPanValueExp, evalCrepFullExp]

theorem compileExp_panOp_mul_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α) (left right : α) :
    compileExp context (.panOp .mul [.const left, .const right]) =
      ([.crepOp .mul [.const left, .const right]], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.panOp .mul [.const left, .const right]) =
      some (.word (left * right)) ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      (.crepOp .mul [.const left, .const right]) =
      some (left * right) := by
  simp [compileExp, compileExp.compileExpList, cexpHeads,
    evalPanValueExp, evalPanValueExp.evalPanValueExps,
    evalCrepFullExp]

theorem compileExp_const_words_list
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (values : List α) :
    compileExp.compileExpList context
        (values.map (fun value => .const value)) =
      values.map (fun value => ([.const value], .one)) := by
  induction values with
  | nil => simp [compileExp.compileExpList]
  | cons value values ih =>
      simp [compileExp.compileExpList, compileExp, ih]

theorem evalPanValueExp_const_words_list
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (values : List α) :
    evalPanValueExp.evalPanValueExps structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord
        (values.map (fun value => .const value)) =
      some (values.map (fun value => .word value)) := by
  induction values with
  | nil => simp [evalPanValueExp.evalPanValueExps]
  | cons value values ih =>
      simp [evalPanValueExp.evalPanValueExps, evalPanValueExp, ih]

theorem compileField_const_words
    [OfNat α 0]
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    compileField index (values.map (fun _ => .one))
        (values.map (fun value => .const value)) =
      ([.const value], .one) := by
  induction values generalizing index value with
  | nil => simp at hfield
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hfield
          subst value
          simp [compileField]
      | succ index =>
          have htail : tail[index]? = some value := by
            simpa using hfield
          simpa [compileField] using ih index value htail

theorem compileExp_rField_const_words_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepLocals : Nat → Option α) (crepMemory : α → Option α)
    (baseAddress topAddress bytesInWord : α)
    (values : List α) (index : Nat) (value : α)
    (hfield : values[index]? = some value) :
    compileExp context
        (.rField index (.rStruct (values.map (fun value => .const value)))) =
      ([.const value], .one) ∧
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rField index (.rStruct (values.map (fun value => .const value)))) =
      some (.word value) ∧
    evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      (.const value) = some value := by
  have hcompileList := compileExp_const_words_list context values
  have hsourceList := evalPanValueExp_const_words_list structs sourceLocals
    sourceGlobals sourceMemory baseAddress topAddress bytesInWord values
  have hfieldCompile := compileField_const_words values index value hfield
  have hflat :
      List.flatMap Prod.fst
        (values.map (fun value =>
            ([CrepExp.const value], Shape.one))) =
        values.map (fun value => CrepExp.const value) := by
    clear hfield hcompileList hsourceList hfieldCompile
    induction values with
    | nil => simp
    | cons head tail ih => simp [ih]
  have hcompile :
      compileExp context
          (.rField index (.rStruct (values.map (fun value => .const value)))) =
        ([.const value], .one) := by
    simpa [compileExp, hcompileList, hflat, Function.comp_def] using hfieldCompile
  have hsource :
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord
          (.rField index (.rStruct (values.map (fun value => .const value)))) =
        some (.word value) := by
    simp only [evalPanValueExp]
    rw [hsourceList]
    simpa using hfield
  exact ⟨hcompile, hsource, by simp [evalCrepFullExp]⟩

end Flapjack
