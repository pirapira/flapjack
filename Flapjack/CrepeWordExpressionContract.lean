import Flapjack.CrepeExpressionRelation

/-!
Bridge the scalar-expression proof interface back to the original Pancake
expression syntax.  `compileSourceWordExp_relation` uses a small auxiliary
datatype so its recursion is structural; this file shows that every `Exp`
accepted by `wordExp` has that representation and packages the resulting
simulation as the contract consumed by program correctness.
-/

namespace Flapjack

def sourceWordExpOf : (expression : Exp α) → wordExp expression → SourceWordExp α
  | .const value, _ => .const value
  | .var .local name, _ => .local name
  | .var .global name, hword => by
      change False at hword
      contradiction
  | .rStruct fields, hword => by
      change False at hword
      contradiction
  | .rField index value, hword => by
      change False at hword
      contradiction
  | .nStruct name fields, hword => by
      change False at hword
      contradiction
  | .nField name value, hword => by
      change False at hword
      contradiction
  | .load shape address, hword => by
      change False at hword
      contradiction
  | .load32 address, hword => by
      change False at hword
      contradiction
  | .loadByte address, hword => by
      change False at hword
      contradiction
  | .op operator arguments, hword =>
      match arguments with
      | [left, right] =>
          let hchildren : wordExp left ∧ wordExp right := by
            simpa only [wordExp] using hword
          .op operator
            (sourceWordExpOf left hchildren.1)
            (sourceWordExpOf right hchildren.2)
      | [] => by
          have hfalse : ¬ wordExp (.op operator ([] : List (Exp α))) := by
            simp [wordExp]
          exact False.elim (hfalse hword)
      | [only] => by
          have hfalse : ¬ wordExp (.op operator [only]) := by
            simp [wordExp]
          exact False.elim (hfalse hword)
      | left :: right :: rest => by
          cases rest with
          | nil =>
              let hchildren : wordExp left ∧ wordExp right := by
                simpa only [wordExp] using hword
              exact .op operator
                (sourceWordExpOf left hchildren.1)
                (sourceWordExpOf right hchildren.2)
          | cons tail rest =>
              have hfalse : ¬ wordExp (.op operator
                  (left :: right :: tail :: rest)) := by
                simp [wordExp]
              exact False.elim (hfalse hword)
  | .panOp operator arguments, hword =>
      match arguments with
      | [left, right] =>
          let hchildren : wordExp left ∧ wordExp right := by
            simpa only [wordExp] using hword
          .mul
            (sourceWordExpOf left hchildren.1)
            (sourceWordExpOf right hchildren.2)
      | [] => by
          have hfalse : ¬ wordExp (.panOp operator ([] : List (Exp α))) := by
            simp [wordExp]
          exact False.elim (hfalse hword)
      | [only] => by
          have hfalse : ¬ wordExp (.panOp operator [only]) := by
            simp [wordExp]
          exact False.elim (hfalse hword)
      | left :: right :: rest => by
          cases rest with
          | nil =>
              let hchildren : wordExp left ∧ wordExp right := by
                simpa only [wordExp] using hword
              exact .mul
                (sourceWordExpOf left hchildren.1)
                (sourceWordExpOf right hchildren.2)
          | cons tail rest =>
              have hfalse : ¬ wordExp (.panOp operator
                  (left :: right :: tail :: rest)) := by
                simp [wordExp]
              exact False.elim (hfalse hword)
  | .cmp operator left right, hword =>
      let hchildren : wordExp left ∧ wordExp right := by
        simpa only [wordExp] using hword
      .cmp operator
        (sourceWordExpOf left hchildren.1)
        (sourceWordExpOf right hchildren.2)
  | .shift operator left right, hword =>
      let hchildren : wordExp left ∧ wordExp right := by
        simpa only [wordExp] using hword
      .shift operator
        (sourceWordExpOf left hchildren.1)
        (sourceWordExpOf right hchildren.2)
  | .baseAddr, _ => .baseAddr
  | .topAddr, _ => .topAddr
  | .bytesInWord, _ => .bytesInWord
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

theorem sourceWordExpOf_toExp : ∀ (expression : Exp α) (hword : wordExp expression),
    (sourceWordExpOf expression hword).toExp = expression
  | .const value, hword => by simp [sourceWordExpOf, SourceWordExp.toExp]
  | .var .local name, hword => by simp [sourceWordExpOf, SourceWordExp.toExp]
  | .var .global name, hword => by
      change False at hword
      contradiction
  | .rStruct fields, hword => by
      change False at hword
      contradiction
  | .rField index value, hword => by
      change False at hword
      contradiction
  | .nStruct name fields, hword => by
      change False at hword
      contradiction
  | .nField name value, hword => by
      change False at hword
      contradiction
  | .load shape address, hword => by
      change False at hword
      contradiction
  | .load32 address, hword => by
      change False at hword
      contradiction
  | .loadByte address, hword => by
      change False at hword
      contradiction
  | .op operator arguments, hword => by
      cases arguments with
      | nil =>
          change False at hword
          contradiction
      | cons left rest =>
          cases rest with
          | nil =>
              change False at hword
              contradiction
          | cons right rest =>
              cases rest with
              | nil =>
                  have hchildren : wordExp left ∧ wordExp right := by
                    simpa only [wordExp] using hword
                  have hleft := sourceWordExpOf_toExp left hchildren.1
                  have hright := sourceWordExpOf_toExp right hchildren.2
                  simp [sourceWordExpOf, SourceWordExp.toExp, hleft, hright]
              | cons tail rest =>
                  change False at hword
                  contradiction
  | .panOp operator arguments, hword => by
      cases arguments with
      | nil =>
          change False at hword
          contradiction
      | cons left rest =>
          cases rest with
          | nil =>
              change False at hword
              contradiction
          | cons right rest =>
              cases rest with
              | nil =>
                  have hchildren : wordExp left ∧ wordExp right := by
                    simpa only [wordExp] using hword
                  have hleft := sourceWordExpOf_toExp left hchildren.1
                  have hright := sourceWordExpOf_toExp right hchildren.2
                  simp [sourceWordExpOf, SourceWordExp.toExp, hleft, hright]
              | cons tail rest =>
                  change False at hword
                  contradiction
  | .cmp operator left right, hword => by
      have hchildren : wordExp left ∧ wordExp right := by
        simpa only [wordExp] using hword
      have hleft := sourceWordExpOf_toExp left hchildren.1
      have hright := sourceWordExpOf_toExp right hchildren.2
      simp [sourceWordExpOf, SourceWordExp.toExp, hleft, hright]
  | .shift operator left right, hword => by
      have hchildren : wordExp left ∧ wordExp right := by
        simpa only [wordExp] using hword
      have hleft := sourceWordExpOf_toExp left hchildren.1
      have hright := sourceWordExpOf_toExp right hchildren.2
      simp [sourceWordExpOf, SourceWordExp.toExp, hleft, hright]
  | .baseAddr, hword => by simp [sourceWordExpOf, SourceWordExp.toExp]
  | .topAddr, hword => by simp [sourceWordExpOf, SourceWordExp.toExp]
  | .bytesInWord, hword => by simp [sourceWordExpOf, SourceWordExp.toExp]

theorem panValueCrepExpressionCorrect_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) (hword : wordExp expression)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionCorrect expression := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨word, hsourceWord⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
    bytesInWord context hrel.2.1
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    (sourceWordExpOf expression hword) sourceValue
    (by simpa [sourceWordExpOf_toExp expression hword] using hsource)
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord
    (hbytesInWord context bytesInWord) hrel.2.1
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    (sourceWordExpOf expression hword) word
    (by
      have hsource' : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression = some (.word word) := by
        simpa [hsourceWord] using hsource
      simpa [sourceWordExpOf_toExp expression hword] using hsource')
  cases hsourceWord
  refine ⟨panValuePayloadWithinLimit_word structs word, [compiled], ?_, ?_⟩
  · simpa [sourceWordExpOf_toExp expression hword, panValueShape] using hcompile
  · simp [hcompiled, evalCrepFullExps, panValueFlatWords,
      panValueFlatWordsFuel]

theorem panValueCrepExpressionStateCorrect_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) (hword : wordExp expression)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepExpressionStateCorrect expression := by
  intro context structs sourceLocals sourceGlobals sourceMemory state
    baseAddress topAddress bytesInWord sourceValue hrel hsource
  obtain ⟨word, hsourceWord⟩ := evalPanValueExp_sourceWord_inv
    structs sourceLocals sourceGlobals sourceMemory baseAddress topAddress
    bytesInWord context hrel.2.1
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    (sourceWordExpOf expression hword) sourceValue
    (by simpa [sourceWordExpOf_toExp expression hword] using hsource)
  have hsource' :
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord expression = some (.word word) := by
    simpa [hsourceWord] using hsource
  have hsourceSourceWord :
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord
        (sourceWordExpOf expression hword).toExp = some (.word word) := by
    simpa [sourceWordExpOf_toExp expression hword] using hsource'
  obtain ⟨compiled, hcompile, hnoGlobal⟩ := compileSourceWordExp_noGlobal
    context structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    (sourceWordExpOf expression hword) word hsourceSourceWord
  obtain ⟨compiled', hcompile', hcompiled'⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord
    (hbytesInWord context bytesInWord)
    hrel.2.1
    (fun name value hvalue => hlookup context sourceLocals name value hvalue)
    (sourceWordExpOf expression hword) word hsourceSourceWord
  have hcompiledEq : compiled = compiled' := by
    have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
      hcompile.symm.trans hcompile'
    exact (List.cons.inj (congrArg Prod.fst hpair)).1
  subst compiled'
  cases hsourceWord
  refine ⟨panValuePayloadWithinLimit_word structs word, [compiled], ?_, ?_⟩
  · simpa [sourceWordExpOf_toExp expression hword, panValueShape] using hcompile
  · have hcompat := evalCrepFullExpsState_eq_of_noGlobals state
      baseAddress topAddress [compiled]
      (by
        intro current hcurrent
        have hcurrent' : current = compiled := by simpa using hcurrent
        simpa [hcurrent'] using hnoGlobal)
    calc
      evalCrepFullExpsState state baseAddress topAddress [compiled] =
          evalCrepFullExps state.locals state.memory
            baseAddress topAddress [compiled] := hcompat
      _ = some [word] := by simp [evalCrepFullExps, hcompiled']
      _ = some (panValueFlatWords (.word word)) := by
        simp [panValueFlatWords, panValueFlatWordsFuel]

end Flapjack
