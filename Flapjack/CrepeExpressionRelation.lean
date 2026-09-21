import Flapjack.CrepeStateRelation
import Flapjack.PanGlobals
import Flapjack.Parser.Localise

/-!
Localisation and the word-expression boundary for the Pancake-to-Crep proof.

`pan_to_crep` is intentionally a post-localisation pass: global variables and
named records have already been removed from the programs it accepts.  The
HOL proof exposes this as `localised_exp`/`localised_prog`; keeping the same
predicates here makes the unsupported compiler fallbacks explicit rather than
silently treating them as ordinary expressions.

The second part is the expression induction interface.  It relates a source
word expression to the single Crep expression emitted for it.  Statement
cases can use this lemma without unfolding either evaluator.
-/

namespace Flapjack

/-! A reusable expression contract for the program correctness induction.  The
state relation is an explicit premise because local variables are represented
by slots in Crep. -/
def PanValueCrepExpressionCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue →
    panValuePayloadWithinLimit structs sourceValue = true ∧
    ∃ compiled,
      compileExp context expression =
        (compiled, panValueShape structs sourceValue) ∧
      evalCrepFullExps state.locals state.memory
        baseAddress topAddress compiled =
        some (panValueFlatWords sourceValue)

/-! State-aware counterpart used while the program proof migrates from the
    compact evaluator.  Its shape is intentionally identical apart from the
    evaluator, so individual expression contracts can be switched over
    independently. -/
def PanValueCrepExpressionStateCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : Exp α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α) (sourceValue : PanValue α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue →
    panValuePayloadWithinLimit structs sourceValue = true ∧
    ∃ compiled,
      compileExp context expression =
        (compiled, panValueShape structs sourceValue) ∧
      evalCrepFullExpsState state baseAddress topAddress compiled =
        some (panValueFlatWords sourceValue)

def localisedExp (expression : Exp α) : Prop :=
  expGlobalVars expression = []

def localisedProg : Prog α → Prop
  | .skip | .break | .continue | .tick | .annot _ _ => True
  | .dec _ _ value body => localisedExp value ∧ localisedProg body
  | .assign .local _ value => localisedExp value
  | .assign .global _ _ => False
  | .primitive _ _ arguments => ∀ expression ∈ arguments, localisedExp expression
  | .store address value | .store32 address value | .storeByte address value |
      .shMemStore _ address value => localisedExp address ∧ localisedExp value
  | .seq first second => localisedProg first ∧ localisedProg second
  | .ite condition thenBranch elseBranch =>
      localisedExp condition ∧ localisedProg thenBranch ∧ localisedProg elseBranch
  | .while condition body => localisedExp condition ∧ localisedProg body
  | .call info _ arguments =>
      (∀ expression ∈ arguments, localisedExp expression) ∧
      (match info with
       | some (some (.global, _), _) => False
       | some (_, some (_, _, handler)) => localisedProg handler
       | _ => True)
  | .decCall _ _ _ arguments body =>
      (∀ expression ∈ arguments, localisedExp expression) ∧ localisedProg body
  | .extCall _ configuration configurationLength array arrayLength =>
      localisedExp configuration ∧ localisedExp configurationLength ∧
      localisedExp array ∧ localisedExp arrayLength
  | .raise _ value | .return value => localisedExp value
  | .shMemLoad _ .local _ address => localisedExp address
  | .shMemLoad _ .global _ _ => False

def wordExp : Exp α → Prop
  | .const _ | .var .local _ | .baseAddr | .topAddr | .bytesInWord => True
  | .op _ [left, right] | .panOp _ [left, right] => wordExp left ∧ wordExp right
  | .cmp _ left right | .shift _ left right => wordExp left ∧ wordExp right
  | _ => False

/-! An auxiliary inductive syntax avoids Lean's nested-inductive restriction
when carrying the expression induction used below.  `toExp` is deliberately
small: it is exactly the scalar expression fragment accepted by Crep. -/
inductive SourceWordExp (α : Type u) where
  | const (value : α)
  | «local» (name : VarName)
  | op (operator : BinOp) (left right : SourceWordExp α)
  | mul (left right : SourceWordExp α)
  | cmp (operator : Cmp) (left right : SourceWordExp α)
  | shift (operator : Shift) (left right : SourceWordExp α)
  | baseAddr
  | topAddr
  | bytesInWord

def SourceWordExp.toExp : SourceWordExp α → Exp α
  | .const value => .const value
  | .«local» name => .var .local name
  | .op operator left right => .op operator [left.toExp, right.toExp]
  | .mul left right => .panOp .mul [left.toExp, right.toExp]
  | .cmp operator left right => .cmp operator left.toExp right.toExp
  | .shift operator left right => .shift operator left.toExp right.toExp
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
  | .bytesInWord => .bytesInWord

theorem SourceWordExp.toExp_word (expression : SourceWordExp α) :
    wordExp expression.toExp := by
  induction expression with
  | const | «local» | baseAddr | topAddr | bytesInWord => simp [SourceWordExp.toExp, wordExp]
  | op operator left right ihLeft ihRight =>
      simp [SourceWordExp.toExp, wordExp, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [SourceWordExp.toExp, wordExp, ihLeft, ihRight]
  | cmp operator left right ihLeft ihRight | shift operator left right ihLeft ihRight =>
      simp [SourceWordExp.toExp, wordExp, ihLeft, ihRight]

/-! Successful evaluation of the scalar expression fragment cannot produce a
structured Pancake value.  This is the source-side inversion used by
program-constructor proofs before they invoke `compileSourceWordExp_relation`.
-/
set_option linter.unusedSimpArgs false in
theorem evalPanValueExp_sourceWord_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (context : CompileContext α)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals
      crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expression : SourceWordExp α) (value : PanValue α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some value) :
    ∃ word, value = .word word := by
  induction expression generalizing value with
  | const constant =>
      simp [SourceWordExp.toExp, evalPanValueExp] at hsource
      exact ⟨constant, hsource.symm⟩
  | «local» name =>
      cases hvalue : sourceLocals name with
      | none =>
          simp [SourceWordExp.toExp, evalPanValueExp, hvalue] at hsource
      | some localValue =>
          cases localValue with
          | word word =>
              refine ⟨word, ?_⟩
              simpa [SourceWordExp.toExp, evalPanValueExp, hvalue] using hsource.symm
          | rStruct fields =>
              obtain ⟨slot, hslot⟩ := hlookup name (.rStruct fields) hvalue
              have hshape := (hlocals name (.rStruct fields) .one [slot]
                hvalue hslot).1
              simp [panValueShape, panShapeMatches] at hshape
          | nStruct structName fields =>
              obtain ⟨slot, hslot⟩ := hlookup name (.nStruct structName fields) hvalue
              have hshape := (hlocals name (.nStruct structName fields) .one [slot]
                hvalue hslot).1
              simp [panValueShape, panShapeMatches] at hshape
  | op operator left right ihLeft ihRight =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [SourceWordExp.toExp, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue =>
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
              baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [SourceWordExp.toExp, evalPanValueExp,
                evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
          | some rightValue =>
              cases leftValue with
              | word leftValue =>
                  cases rightValue with
                  | word rightValue =>
                      refine ⟨evalPanBinOp operator leftValue rightValue, ?_⟩
                      simpa [SourceWordExp.toExp, evalPanValueExp,
                        evalPanValueExp.evalPanValueExps, hleft, hright] using hsource.symm
                  | rStruct fields =>
                      simp [SourceWordExp.toExp, evalPanValueExp,
                        evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
                  | nStruct name fields =>
                      simp [SourceWordExp.toExp, evalPanValueExp,
                        evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
              | rStruct fields =>
                  simp [SourceWordExp.toExp, evalPanValueExp,
                    evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
              | nStruct name fields =>
                  simp [SourceWordExp.toExp, evalPanValueExp,
                    evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
  | mul left right ihLeft ihRight =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [SourceWordExp.toExp, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue =>
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
              baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [SourceWordExp.toExp, evalPanValueExp,
                evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
          | some rightValue =>
              cases leftValue with
              | word leftValue =>
                  cases rightValue with
                  | word rightValue =>
                      refine ⟨leftValue * rightValue, ?_⟩
                      simpa [SourceWordExp.toExp, evalPanValueExp,
                        evalPanValueExp.evalPanValueExps, hleft, hright] using hsource.symm
                  | rStruct fields | nStruct _ fields =>
                      simp [SourceWordExp.toExp, evalPanValueExp,
                        evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
              | rStruct fields | nStruct _ fields =>
                  simp [SourceWordExp.toExp, evalPanValueExp,
                    evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
  | cmp operator left right ihLeft ihRight =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [SourceWordExp.toExp, evalPanValueExp, hleft] at hsource
      | some leftValue =>
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
              baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
          | some rightValue =>
              cases leftValue with
              | word leftValue =>
                  cases rightValue with
                  | word rightValue =>
                      refine ⟨evalPanCmp operator leftValue rightValue, ?_⟩
                      simpa [SourceWordExp.toExp, evalPanValueExp, hleft, hright] using hsource.symm
                  | rStruct fields | nStruct _ fields =>
                      simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
              | rStruct fields | nStruct _ fields =>
                  simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
  | shift operator left right ihLeft ihRight =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [SourceWordExp.toExp, evalPanValueExp, hleft] at hsource
      | some leftValue =>
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
              baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
          | some rightValue =>
              cases leftValue with
              | word leftValue =>
                  cases rightValue with
                  | word rightValue =>
                      cases hshift : evalPanShift operator leftValue rightValue with
                      | none =>
                          simp [SourceWordExp.toExp, evalPanValueExp,
                            hleft, hright, hshift] at hsource
                      | some shifted =>
                          refine ⟨shifted, ?_⟩
                          simpa [SourceWordExp.toExp, evalPanValueExp,
                            hleft, hright, hshift] using hsource.symm
                  | rStruct fields | nStruct _ fields =>
                      simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
              | rStruct fields | nStruct _ fields =>
                  simp [SourceWordExp.toExp, evalPanValueExp, hleft, hright] at hsource
  | baseAddr =>
      simp [SourceWordExp.toExp, evalPanValueExp] at hsource
      exact ⟨baseAddress, hsource.symm⟩
  | topAddr =>
      simp [SourceWordExp.toExp, evalPanValueExp] at hsource
      exact ⟨topAddress, hsource.symm⟩
  | bytesInWord =>
      simp [SourceWordExp.toExp, evalPanValueExp] at hsource
      exact ⟨bytesInWord, hsource.symm⟩
theorem localisedExp_iff_no_global (expression : Exp α) :
    localisedExp expression ↔ expGlobalVars expression = [] := by
  rfl

theorem localisedProg_assign_global_false (name : VarName) (value : Exp α) :
    ¬ localisedProg (.assign .global name value : Prog α) := by
  simp [localisedProg]

/-- A list of expressions all of which are localised has no global variables. -/
theorem expGlobalVarsList_eq_nil_of_all_localised (expressions : List (Exp α))
    (h : ∀ expression ∈ expressions, localisedExp expression) :
    expGlobalVars.expGlobalVarsList expressions = [] := by
  induction expressions with
  | nil => simp [expGlobalVars.expGlobalVarsList]
  | cons head tail ih =>
      simp only [expGlobalVars.expGlobalVarsList]
      rw [h head (by simp), List.nil_append]
      exact ih (fun expression hmem => h expression (by simp [hmem]))

/-- Counterpart of the first conjunct of Cake's `localised_exp_shape_val`
    (`pan_globalsProofScript.sml:3207`): the placeholder expression generated
    for a shape is localised. -/
theorem localisedExp_shapeVal (shape : Shape) : localisedExp (shapeVal shape) := by
  have hmain : ∀ shape : Shape, localisedExp (shapeVal shape) := by
    apply shapeVal.induct
      (motive1 := fun shape => localisedExp (shapeVal shape))
      (motive2 := fun shapes => ∀ expression ∈ shapeVals shapes,
        localisedExp expression)
    · simp [shapeVal, localisedExp, expGlobalVars]
    · intro shapes ih
      simp only [shapeVal]
      simpa only [localisedExp, expGlobalVars] using
        expGlobalVarsList_eq_nil_of_all_localised (shapeVals shapes) ih
    · intro name
      simp [shapeVal, localisedExp, expGlobalVars]
    · simp [shapeVals]
    · intro shape shapes ihHead ihTail expression hmem
      simp only [shapeVals, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ihHead
      · exact ihTail expression hmem
  exact hmain shape

/-- Counterpart of the second conjunct of Cake's `localised_exp_shape_val`
    (`pan_globalsProofScript.sml:3207`): every placeholder expression in a list
    generated for a shape list is localised. -/
theorem localisedExp_shapeVals (shapes : List Shape) :
    ∀ expression ∈ shapeVals shapes, localisedExp expression := by
  induction shapes with
  | nil => simp [shapeVals]
  | cons shape shapes ih =>
      intro expression hmem
      simp only [shapeVals, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact localisedExp_shapeVal shape
      · exact ih expression hmem

/-- The `pan_globals` expression compiler never introduces a global variable:
    every global read is replaced by a load from the address derived from
    `topAddr`, and `topAddr` itself carries no global variable. -/
theorem globalCompileExp_expGlobalVars [BEq String] (context : GlobalPassContext α)
    (expression : Exp α) :
    expGlobalVars (globalCompileExp context expression) = [] := by
  have hmain : ∀ expression : Exp α,
      expGlobalVars (globalCompileExp context expression) = [] := by
    apply globalCompileExp.induct context
      (motive1 := fun expressions =>
        expGlobalVars.expGlobalVarsList
          (globalCompileExp.globalCompileExps context expressions) = [])
      (motive2 := fun expression =>
        expGlobalVars (globalCompileExp context expression) = [])
    · simp [globalCompileExp.globalCompileExps, expGlobalVars.expGlobalVarsList]
    · intro expression expressions ihExpr ihExprs
      simp only [globalCompileExp.globalCompileExps, expGlobalVars.expGlobalVarsList]
      rw [ihExpr, ihExprs]
      simp
    · intro name
      rw [globalCompileExp_local]
      simp [expGlobalVars]
    · intro name shape address hlookup
      have hcomp : globalCompileExp context (.var .global name) =
          .load shape (.op .sub [.topAddr, .const address]) := by
        simp [globalCompileExp, hlookup]
      rw [hcomp]
      simp [expGlobalVars, expGlobalVars.expGlobalVarsList]
    · intro name hlookup
      have hcomp : globalCompileExp context (.var .global name) =
          .const (context.fromNat 0) := by
        simp [globalCompileExp, hlookup]
      rw [hcomp]
      simp [expGlobalVars]
    · intro expressions ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro index expression ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro name fields
      simp [globalCompileExp, expGlobalVars]
    · intro name value
      simp [globalCompileExp, expGlobalVars]
    · intro shape address ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro address ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro address ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro operator expressions ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro operator expressions ih
      simpa only [globalCompileExp, expGlobalVars] using ih
    · intro operator left right ihL ihR
      simp only [globalCompileExp, expGlobalVars]
      rw [ihL, ihR]
      simp
    · intro operator left right ihL ihR
      simp only [globalCompileExp, expGlobalVars]
      rw [ihL, ihR]
      simp
    · simp [globalCompileExp, expGlobalVars, expGlobalVars.expGlobalVarsList]
    · intro expression hlocal hglobal hrstruct hrfield hnstruct hnfield hload hload32
        hloadbyte hop hpanop hcmp hshift htop
      cases expression with
      | const value => simp [globalCompileExp, expGlobalVars]
      | baseAddr => simp [globalCompileExp, expGlobalVars]
      | bytesInWord => simp [globalCompileExp, expGlobalVars]
      | var kind name => cases kind <;> simp_all
      | rStruct fields => exact absurd rfl (hrstruct fields)
      | rField index value => exact absurd rfl (hrfield index value)
      | nStruct name fields => exact absurd rfl (hnstruct name fields)
      | nField name value => exact absurd rfl (hnfield name value)
      | load shape address => exact absurd rfl (hload shape address)
      | load32 address => exact absurd rfl (hload32 address)
      | loadByte address => exact absurd rfl (hloadbyte address)
      | op operator args => exact absurd rfl (hop operator args)
      | panOp operator args => exact absurd rfl (hpanop operator args)
      | cmp operator left right => exact absurd rfl (hcmp operator left right)
      | shift operator left right => exact absurd rfl (hshift operator left right)
      | topAddr => exact absurd rfl htop
  exact hmain expression

/-- List form of `globalCompileExp_expGlobalVars`. -/
theorem globalCompileExps_expGlobalVars [BEq String] (context : GlobalPassContext α)
    (expressions : List (Exp α)) :
    expGlobalVars.expGlobalVarsList
      (globalCompileExp.globalCompileExps context expressions) = [] := by
  induction expressions with
  | nil => simp [globalCompileExp.globalCompileExps, expGlobalVars.expGlobalVarsList]
  | cons expression expressions ih =>
      simp only [globalCompileExp.globalCompileExps, expGlobalVars.expGlobalVarsList]
      rw [globalCompileExp_expGlobalVars, ih]
      simp

/-- Counterpart of Cake's `compile_exp_localised`
    (`pan_globalsProofScript.sml:3196`): the `pan_globals` expression compiler
    always produces a localised expression. -/
theorem globalCompileExp_localised [BEq String] (context : GlobalPassContext α)
    (expression : Exp α) :
    localisedExp (globalCompileExp context expression) := by
  simpa [localisedExp] using globalCompileExp_expGlobalVars context expression

/-- A value placeholder generated for a shape is localised, in the
    `pan_globals` context used by `globalCompileProg`.  This is the
    `pan_globals` counterpart of the first conjunct of Cake's
    `localised_exp_shape_val` (`pan_globalsProofScript.sml:3216` context). -/
theorem globalShapeVal_localised [BEq String] (context : GlobalPassContext α)
    (shape : Shape) : localisedExp (globalShapeVal context shape) := by
  have hmain : ∀ shape : Shape, localisedExp (globalShapeVal context shape) := by
    apply globalShapeVal.induct
      (motive := fun shape => localisedExp (globalShapeVal context shape))
    · simp [globalShapeVal, localisedExp, expGlobalVars]
    · intro name
      simp [globalShapeVal, localisedExp, expGlobalVars]
    · intro shapes ih
      simp only [globalShapeVal]
      have hmap : ∀ expression ∈ shapes.map (globalShapeVal context),
          localisedExp expression := by
        intro expression hmem
        obtain ⟨shape, hshape, rfl⟩ := List.mem_map.mp hmem
        exact ih shape hshape
      simpa only [localisedExp, expGlobalVars] using
        expGlobalVarsList_eq_nil_of_all_localised
          (shapes.map (globalShapeVal context)) hmap
  exact hmain shape

/-- Counterpart of Cake's `nested_seqs_localised`
    (`pan_globalsProofScript.sml:3253`): a nested sequence is localised exactly
    when every one of its statements is. -/
theorem nestedSeq_localised (statements : List (Prog α)) :
    localisedProg (nestedSeq statements) ↔
      ∀ statement ∈ statements, localisedProg statement := by
  induction statements with
  | nil => simp [nestedSeq, localisedProg]
  | cons statement statements ih => simp [nestedSeq, localisedProg, ih]

/-! Successful word operations cannot hide a failed or structured operand.
This is the source-side inversion lemma needed before applying the
compositional operation boundaries below. -/
set_option linter.unnecessarySimpa false in
theorem evalPanValueExp_op_word_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (operator : BinOp)
    (left right : Exp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.op operator [left, right]) =
      some (.word value)) :
    ∃ leftValue rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left = some (.word leftValue) ∧
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right = some (.word rightValue) ∧
      evalPanBinOp operator leftValue rightValue = value := by
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left with
  | none =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleft] at hsource
  | some leftValue =>
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord right with
      | none =>
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleft, hright] at hsource
      | some rightValue =>
          cases leftValue with
          | word leftValue =>
              cases rightValue with
              | word rightValue =>
                  refine ⟨leftValue, rightValue, ?_, ?_, ?_⟩
                  · simpa using hleft
                  · simpa using hright
                  simpa [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] using hsource
              | rStruct fields =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] at hsource
              | nStruct name fields =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] at hsource
          | rStruct fields =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleft, hright] at hsource
          | nStruct name fields =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleft, hright] at hsource

set_option linter.unnecessarySimpa false in
theorem evalPanValueExp_mul_word_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (left right : Exp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.panOp .mul [left, right]) =
      some (.word value)) :
    ∃ leftValue rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left = some (.word leftValue) ∧
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right = some (.word rightValue) ∧
      leftValue * rightValue = value := by
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left with
  | none =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleft] at hsource
  | some leftValue =>
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord right with
      | none =>
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleft, hright] at hsource
      | some rightValue =>
          cases leftValue with
          | word leftValue =>
              cases rightValue with
              | word rightValue =>
                  refine ⟨leftValue, rightValue, ?_, ?_, ?_⟩
                  · simpa using hleft
                  · simpa using hright
                  have hvalue' := hsource
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] at hvalue'
                  exact hvalue'
              | rStruct fields =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] at hsource
              | nStruct name fields =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleft, hright] at hsource
          | rStruct fields =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleft, hright] at hsource
          | nStruct name fields =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleft, hright] at hsource

set_option linter.unnecessarySimpa false in
theorem evalPanValueExp_cmp_word_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (operator : Cmp)
    (left right : Exp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.cmp operator left right) =
      some (.word value)) :
    ∃ leftValue rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left = some (.word leftValue) ∧
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right = some (.word rightValue) ∧
      evalPanCmp operator leftValue rightValue = value := by
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left with
  | none =>
      simp [evalPanValueExp, hleft] at hsource
  | some leftValue =>
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord right with
      | none =>
          simp [evalPanValueExp, hleft, hright] at hsource
      | some rightValue =>
          cases leftValue with
          | word leftValue =>
              cases rightValue with
              | word rightValue =>
                  refine ⟨leftValue, rightValue, ?_, ?_, ?_⟩
                  · simpa using hleft
                  · simpa using hright
                  have hvalue' := hsource
                  simp [evalPanValueExp, hleft, hright] at hvalue'
                  exact hvalue'
              | rStruct fields => simp [evalPanValueExp, hleft, hright] at hsource
              | nStruct name fields => simp [evalPanValueExp, hleft, hright] at hsource
          | rStruct fields => simp [evalPanValueExp, hleft, hright] at hsource
          | nStruct name fields => simp [evalPanValueExp, hleft, hright] at hsource

set_option linter.unnecessarySimpa false in
theorem evalPanValueExp_shift_word_inv
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (operator : Shift)
    (left right : Exp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.shift operator left right) =
      some (.word value)) :
    ∃ leftValue rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left = some (.word leftValue) ∧
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right = some (.word rightValue) ∧
      evalPanShift operator leftValue rightValue = some value := by
  cases hleft : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left with
  | none => simp [evalPanValueExp, hleft] at hsource
  | some leftValue =>
      cases hright : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord right with
      | none => simp [evalPanValueExp, hleft, hright] at hsource
      | some rightValue =>
          cases leftValue with
          | word leftValue =>
              cases rightValue with
              | word rightValue =>
                  refine ⟨leftValue, rightValue, ?_, ?_, ?_⟩
                  · simpa using hleft
                  · simpa using hright
                  have hvalue' := hsource
                  simp [evalPanValueExp, hleft, hright] at hvalue'
                  exact hvalue'
              | rStruct fields => simp [evalPanValueExp, hleft, hright] at hsource
              | nStruct name fields => simp [evalPanValueExp, hleft, hright] at hsource
          | rStruct fields => simp [evalPanValueExp, hleft, hright] at hsource
          | nStruct name fields => simp [evalPanValueExp, hleft, hright] at hsource

/-! The local-variable leaf of the source expression simulation.  The
compiler-context lookup is deliberately an explicit premise: it is the Lean
counterpart of the HOL proof's `FLOOKUP ctxt.vars` obligation. -/
theorem compileSourceWordExp_local_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (name : VarName) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord (.var .local name) = some (.word value))
    (hlookup : ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals) :
    ∃ slot,
      compileExp context (.var .local name) = ([.var slot], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress (.var slot) =
        some value := by
  obtain ⟨slot, hslot⟩ := hlookup
  have hsource' : sourceLocals name = some (.word value) := by
    simpa [evalPanValueExp] using hsource
  have hrel := hlocals name (.word value) .one [slot] hsource' hslot
  refine ⟨slot, ?_, ?_⟩
  · simp [compileExp, hslot]
  · have hslotValue : crepLocals slot = some value := by
      cases hslotValue : crepLocals slot with
      | none => simp [readCrepLocals, hslotValue] at hrel
      | some current =>
          simp [readCrepLocals, hslotValue, panValueFlatWords,
            panValueFlatWordsFuel] at hrel ⊢
          simpa using hrel.2
    simpa [evalCrepFullExp] using hslotValue

/-! Binary operations compose the two child expression witnesses.  The source
and target equations are intentionally both hypotheses here; the upcoming
recursive expression theorem will obtain them from its induction hypotheses. -/
theorem compileSourceWordExp_op_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : BinOp) (left right : SourceWordExp α)
    (leftCompiled rightCompiled : CrepExp α)
    (leftValue rightValue value : α)
    (hleftSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp = some (.word leftValue))
    (hrightSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord right.toExp = some (.word rightValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.op operator [left.toExp, right.toExp]) = some (.word value))
    (hleftCompile : compileExp context left.toExp = ([leftCompiled], .one))
    (hrightCompile : compileExp context right.toExp = ([rightCompiled], .one))
    (hleftEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      leftCompiled = some leftValue)
    (hrightEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      rightCompiled = some rightValue) :
    compileExp context (.op operator [left.toExp, right.toExp]) =
        ([.op operator [leftCompiled, rightCompiled]], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress
        (.op operator [leftCompiled, rightCompiled]) = some value := by
  have hvalue : evalPanBinOp operator leftValue rightValue = value := by
    have hvalue' := hsource
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
      hleftSource, hrightSource] at hvalue'
    exact hvalue'
  constructor
  · simp [compileExp, compileExp.compileExpList, cexpHeads,
      hleftCompile, hrightCompile]
  · simp [evalCrepFullExp, hleftEval, hrightEval, hvalue]

theorem compileSourceWordExp_mul_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (left right : SourceWordExp α)
    (leftCompiled rightCompiled : CrepExp α)
    (leftValue rightValue value : α)
    (hleftSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp = some (.word leftValue))
    (hrightSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord right.toExp = some (.word rightValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.panOp .mul [left.toExp, right.toExp]) = some (.word value))
    (hleftCompile : compileExp context left.toExp = ([leftCompiled], .one))
    (hrightCompile : compileExp context right.toExp = ([rightCompiled], .one))
    (hleftEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      leftCompiled = some leftValue)
    (hrightEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      rightCompiled = some rightValue) :
    compileExp context (.panOp .mul [left.toExp, right.toExp]) =
        ([.crepOp .mul [leftCompiled, rightCompiled]], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress
        (.crepOp .mul [leftCompiled, rightCompiled]) = some value := by
  have hvalue : leftValue * rightValue = value := by
    have hvalue' := hsource
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
      hleftSource, hrightSource] at hvalue'
    exact hvalue'
  constructor
  · simp [compileExp, compileExp.compileExpList, cexpHeads,
      hleftCompile, hrightCompile]
  · simp [evalCrepFullExp, hleftEval, hrightEval, hvalue]

theorem compileSourceWordExp_mul_recursive_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (left right : SourceWordExp α) (value : α)
    (hleftRelation : ∀ leftValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left.toExp = some (.word leftValue) →
      ∃ compiled,
        compileExp context left.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some leftValue)
    (hrightRelation : ∀ rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right.toExp = some (.word rightValue) →
      ∃ compiled,
        compileExp context right.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some rightValue)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.panOp .mul [left.toExp, right.toExp]) = some (.word value)) :
    ∃ compiled,
      compileExp context (.panOp .mul [left.toExp, right.toExp]) =
        ([compiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
        some value := by
  obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
    evalPanValueExp_mul_word_inv structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp right.toExp value hsource
  obtain ⟨leftCompiled, hleftCompile, hleftEval⟩ :=
    hleftRelation leftValue hleftSource
  obtain ⟨rightCompiled, hrightCompile, hrightEval⟩ :=
    hrightRelation rightValue hrightSource
  have hmul := compileSourceWordExp_mul_relation context structs sourceLocals
    sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
    bytesInWord left right leftCompiled rightCompiled leftValue rightValue value
    hleftSource hrightSource hsource hleftCompile hrightCompile hleftEval
    hrightEval
  exact ⟨.crepOp .mul [leftCompiled, rightCompiled], hmul.1, hmul.2⟩

theorem compileSourceWordExp_cmp_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : Cmp) (left right : SourceWordExp α)
    (leftCompiled rightCompiled : CrepExp α)
    (leftValue rightValue value : α)
    (hleftSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp = some (.word leftValue))
    (hrightSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord right.toExp = some (.word rightValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.cmp operator left.toExp right.toExp) = some (.word value))
    (hleftCompile : compileExp context left.toExp = ([leftCompiled], .one))
    (hrightCompile : compileExp context right.toExp = ([rightCompiled], .one))
    (hleftEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      leftCompiled = some leftValue)
    (hrightEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      rightCompiled = some rightValue) :
    compileExp context (.cmp operator left.toExp right.toExp) =
        ([.cmp operator leftCompiled rightCompiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress
        (.cmp operator leftCompiled rightCompiled) = some value := by
  have hvalue : evalPanCmp operator leftValue rightValue = value := by
    have hvalue' := hsource
    simp [evalPanValueExp, hleftSource, hrightSource] at hvalue'
    exact hvalue'
  constructor
  · simp [compileExp, hleftCompile, hrightCompile]
  · simp [evalCrepFullExp, hleftEval, hrightEval, hvalue]

theorem compileSourceWordExp_cmp_recursive_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : Cmp) (left right : SourceWordExp α) (value : α)
    (hleftRelation : ∀ leftValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left.toExp = some (.word leftValue) →
      ∃ compiled,
        compileExp context left.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some leftValue)
    (hrightRelation : ∀ rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right.toExp = some (.word rightValue) →
      ∃ compiled,
        compileExp context right.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some rightValue)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.cmp operator left.toExp right.toExp) = some (.word value)) :
    ∃ compiled,
      compileExp context (.cmp operator left.toExp right.toExp) =
        ([compiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
        some value := by
  obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
    evalPanValueExp_cmp_word_inv structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
  obtain ⟨leftCompiled, hleftCompile, hleftEval⟩ :=
    hleftRelation leftValue hleftSource
  obtain ⟨rightCompiled, hrightCompile, hrightEval⟩ :=
    hrightRelation rightValue hrightSource
  have hcmp := compileSourceWordExp_cmp_relation context structs sourceLocals
    sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
    bytesInWord operator left right leftCompiled rightCompiled leftValue rightValue
    value hleftSource hrightSource hsource hleftCompile hrightCompile hleftEval
    hrightEval
  exact ⟨.cmp operator leftCompiled rightCompiled, hcmp.1, hcmp.2⟩

theorem compileSourceWordExp_shift_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : Shift) (left right : SourceWordExp α)
    (leftCompiled rightCompiled : CrepExp α)
    (leftValue rightValue value : α)
    (hleftSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord left.toExp = some (.word leftValue))
    (hrightSource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord right.toExp = some (.word rightValue))
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.shift operator left.toExp right.toExp) = some (.word value))
    (hleftCompile : compileExp context left.toExp = ([leftCompiled], .one))
    (hrightCompile : compileExp context right.toExp = ([rightCompiled], .one))
    (hleftEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      leftCompiled = some leftValue)
    (hrightEval : evalCrepFullExp crepLocals crepMemory baseAddress topAddress
      rightCompiled = some rightValue) :
    compileExp context (.shift operator left.toExp right.toExp) =
        ([.shift operator leftCompiled rightCompiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress
        (.shift operator leftCompiled rightCompiled) = some value := by
  have hvalue : evalPanShift operator leftValue rightValue = some value := by
    have hvalue' := hsource
    simp [evalPanValueExp, hleftSource, hrightSource] at hvalue'
    cases hshift : evalPanShift operator leftValue rightValue with
    | none => simp [hshift] at hvalue'
    | some shifted =>
        simp [hshift] at hvalue'
        exact congrArg some hvalue'
  constructor
  · simp [compileExp, hleftCompile, hrightCompile]
  · simp [evalCrepFullExp, hleftEval, hrightEval, hvalue]

theorem compileSourceWordExp_shift_recursive_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : Shift) (left right : SourceWordExp α) (value : α)
    (hleftRelation : ∀ leftValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left.toExp = some (.word leftValue) →
      ∃ compiled,
        compileExp context left.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some leftValue)
    (hrightRelation : ∀ rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right.toExp = some (.word rightValue) →
      ∃ compiled,
        compileExp context right.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some rightValue)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.shift operator left.toExp right.toExp) = some (.word value)) :
    ∃ compiled,
      compileExp context (.shift operator left.toExp right.toExp) =
        ([compiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
        some value := by
  obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
    evalPanValueExp_shift_word_inv structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
  obtain ⟨leftCompiled, hleftCompile, hleftEval⟩ :=
    hleftRelation leftValue hleftSource
  obtain ⟨rightCompiled, hrightCompile, hrightEval⟩ :=
    hrightRelation rightValue hrightSource
  have hshift := compileSourceWordExp_shift_relation context structs sourceLocals
    sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
    bytesInWord operator left right leftCompiled rightCompiled leftValue rightValue
    value hleftSource hrightSource hsource hleftCompile hrightCompile hleftEval
    hrightEval
  exact ⟨.shift operator leftCompiled rightCompiled, hshift.1, hshift.2⟩

/-! Recursive binary-operation composition.  This is the exact induction
interface needed when a localized Pancake expression is decomposed into its
word-expression children. -/
theorem compileSourceWordExp_op_recursive_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (operator : BinOp) (left right : SourceWordExp α) (value : α)
    (hleftRelation : ∀ leftValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord left.toExp = some (.word leftValue) →
      ∃ compiled,
        compileExp context left.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some leftValue)
    (hrightRelation : ∀ rightValue,
      evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord right.toExp = some (.word rightValue) →
      ∃ compiled,
        compileExp context right.toExp = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some rightValue)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.op operator [left.toExp, right.toExp]) = some (.word value)) :
    ∃ compiled,
      compileExp context (.op operator [left.toExp, right.toExp]) =
        ([compiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
        some value := by
  obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
    evalPanValueExp_op_word_inv structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
  obtain ⟨leftCompiled, hleftCompile, hleftEval⟩ :=
    hleftRelation leftValue hleftSource
  obtain ⟨rightCompiled, hrightCompile, hrightEval⟩ :=
    hrightRelation rightValue hrightSource
  have hop := compileSourceWordExp_op_relation context structs sourceLocals
    sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
    bytesInWord operator left right leftCompiled rightCompiled leftValue rightValue
    value hleftSource hrightSource hsource hleftCompile hrightCompile hleftEval
    hrightEval
  exact ⟨.op operator [leftCompiled, rightCompiled], hop.1, hop.2⟩

/-! Unified scalar expression simulation.  The source expression is represented
by `SourceWordExp` so this induction is structural, while the generated Crep
expression and its evaluation are ordinary Pancake objects. -/
theorem compileSourceWordExp_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepLocals : Nat → Option α)
    (crepMemory : α → Option α) (baseAddress topAddress bytesInWord : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expression : SourceWordExp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    ∃ compiled, compileExp context expression.toExp = ([compiled], .one) ∧
      evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
        some value := by
  induction expression generalizing value with
  | const constant =>
      have hvalue : constant = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.const constant, by simp [SourceWordExp.toExp, compileExp],
        by simp [evalCrepFullExp]⟩
  | «local» name =>
      have hsource' : sourceLocals name = some (.word value) := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      change ∃ compiled, compileExp context (.var .local name) = ([compiled], .one) ∧
        evalCrepFullExp crepLocals crepMemory baseAddress topAddress compiled =
          some value
      obtain ⟨slot, hcompile, heval⟩ :=
        compileSourceWordExp_local_relation context structs sourceLocals
        sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
        bytesInWord name value hsource (hlookup name (.word value) hsource') hlocals
      exact ⟨.var slot, hcompile, heval⟩
  | op operator left right ihLeft ihRight =>
      exact compileSourceWordExp_op_recursive_relation context structs sourceLocals
        sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
        bytesInWord operator left right value
        (fun leftValue hleft => ihLeft leftValue hleft)
        (fun rightValue hright => ihRight rightValue hright) hsource
  | mul left right ihLeft ihRight =>
      exact compileSourceWordExp_mul_recursive_relation context structs sourceLocals
        sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
        bytesInWord left right value
        (fun leftValue hleft => ihLeft leftValue hleft)
        (fun rightValue hright => ihRight rightValue hright) hsource
  | cmp operator left right ihLeft ihRight =>
      exact compileSourceWordExp_cmp_recursive_relation context structs sourceLocals
        sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
        bytesInWord operator left right value
        (fun leftValue hleft => ihLeft leftValue hleft)
        (fun rightValue hright => ihRight rightValue hright) hsource
  | shift operator left right ihLeft ihRight =>
      exact compileSourceWordExp_shift_recursive_relation context structs sourceLocals
        sourceGlobals sourceMemory crepLocals crepMemory baseAddress topAddress
        bytesInWord operator left right value
        (fun leftValue hleft => ihLeft leftValue hleft)
        (fun rightValue hright => ihRight rightValue hright) hsource
  | baseAddr =>
      have hvalue : baseAddress = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.baseAddr, by simp [SourceWordExp.toExp, compileExp],
        by simp [evalCrepFullExp]⟩
  | topAddr =>
      have hvalue : topAddress = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.topAddr, by simp [SourceWordExp.toExp, compileExp],
        by simp [evalCrepFullExp]⟩
  | bytesInWord =>
      have hvalue : bytesInWord = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.const context.bytesInWord, by simp [SourceWordExp.toExp, compileExp],
        by simp [hbytesInWord, evalCrepFullExp]⟩

/-! The scalar compiler relation also gives a syntactic guarantee: generated
    expressions in this fragment never read the separate Crep global area. -/
theorem compileSourceWordExp_noGlobal
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expression : SourceWordExp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value)) :
    ∃ compiled, compileExp context expression.toExp = ([compiled], .one) ∧
      CrepExpNoGlobal compiled := by
  induction expression generalizing value with
  | const constant =>
      have hvalue : constant = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.const constant, by simp [SourceWordExp.toExp, compileExp], .const _⟩
  | «local» name =>
      have hsource' : sourceLocals name = some (.word value) := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      obtain ⟨slot, hslot⟩ := hlookup name (.word value) hsource'
      refine ⟨.var slot, ?_, .var _⟩
      simp [SourceWordExp.toExp, compileExp, hslot]
  | op operator left right ihLeft ihRight =>
      obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
        evalPanValueExp_op_word_inv structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
      obtain ⟨leftCompiled, hleftCompile, hleftNoGlobal⟩ :=
        ihLeft leftValue hleftSource
      obtain ⟨rightCompiled, hrightCompile, hrightNoGlobal⟩ :=
        ihRight rightValue hrightSource
      refine ⟨.op operator [leftCompiled, rightCompiled], ?_,
        .op hleftNoGlobal hrightNoGlobal⟩
      simp [SourceWordExp.toExp, compileExp, compileExp.compileExpList,
        cexpHeads, hleftCompile, hrightCompile]
  | mul left right ihLeft ihRight =>
      obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
        evalPanValueExp_mul_word_inv structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord left.toExp right.toExp value hsource
      obtain ⟨leftCompiled, hleftCompile, hleftNoGlobal⟩ :=
        ihLeft leftValue hleftSource
      obtain ⟨rightCompiled, hrightCompile, hrightNoGlobal⟩ :=
        ihRight rightValue hrightSource
      refine ⟨.crepOp .mul [leftCompiled, rightCompiled], ?_,
        .crepMul hleftNoGlobal hrightNoGlobal⟩
      simp [SourceWordExp.toExp, compileExp, compileExp.compileExpList,
        cexpHeads, hleftCompile, hrightCompile]
  | cmp operator left right ihLeft ihRight =>
      obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
        evalPanValueExp_cmp_word_inv structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
      obtain ⟨leftCompiled, hleftCompile, hleftNoGlobal⟩ :=
        ihLeft leftValue hleftSource
      obtain ⟨rightCompiled, hrightCompile, hrightNoGlobal⟩ :=
        ihRight rightValue hrightSource
      refine ⟨.cmp operator leftCompiled rightCompiled, ?_,
        .cmp hleftNoGlobal hrightNoGlobal⟩
      simp [SourceWordExp.toExp, compileExp, hleftCompile, hrightCompile]
  | shift operator left right ihLeft ihRight =>
      obtain ⟨leftValue, rightValue, hleftSource, hrightSource, _⟩ :=
        evalPanValueExp_shift_word_inv structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord operator left.toExp right.toExp value hsource
      obtain ⟨leftCompiled, hleftCompile, hleftNoGlobal⟩ :=
        ihLeft leftValue hleftSource
      obtain ⟨rightCompiled, hrightCompile, hrightNoGlobal⟩ :=
        ihRight rightValue hrightSource
      refine ⟨.shift operator leftCompiled rightCompiled, ?_,
        .shift hleftNoGlobal hrightNoGlobal⟩
      simp [SourceWordExp.toExp, compileExp, hleftCompile, hrightCompile]
  | baseAddr =>
      have hvalue : baseAddress = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.baseAddr, by simp [SourceWordExp.toExp, compileExp], .baseAddr⟩
  | topAddr =>
      have hvalue : topAddress = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.topAddr, by simp [SourceWordExp.toExp, compileExp], .topAddr⟩
  | bytesInWord =>
      have hvalue : bytesInWord = value := by
        simpa [SourceWordExp.toExp, evalPanValueExp] using hsource
      subst value
      exact ⟨.const context.bytesInWord,
        by simp [SourceWordExp.toExp, compileExp], .const _⟩

/-! Stateful form of the scalar expression relation.  The compiler relation
itself is unchanged; the no-global witness transports the compact evaluator
result to the explicit global-aware evaluator. -/
theorem compileSourceWordExp_state_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (baseAddress topAddress bytesInWord : α)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepLocalsRel structs context sourceLocals state.locals)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (expression : SourceWordExp α) (value : α)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp =
      some (.word value)) :
    ∃ compiled, compileExp context expression.toExp = ([compiled], .one) ∧
      evalCrepFullExpState state baseAddress topAddress compiled = some value := by
  obtain ⟨compiled, hcompile, hcompiled⟩ := compileSourceWordExp_relation
    context structs sourceLocals sourceGlobals sourceMemory state.locals state.memory
    baseAddress topAddress bytesInWord hbytesInWord hlocals hlookup expression value hsource
  obtain ⟨compiled', hcompile', hnoGlobal⟩ := compileSourceWordExp_noGlobal
    context structs sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord hlookup expression value hsource
  have hcompiledEq : compiled = compiled' := by
    have hpair : ([compiled], Shape.one) = ([compiled'], Shape.one) :=
      hcompile.symm.trans hcompile'
    exact (List.cons.inj (congrArg Prod.fst hpair)).1
  refine ⟨compiled, hcompile, ?_⟩
  rw [hcompiledEq]
  rw [evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
    compiled' hnoGlobal]
  simpa [hcompiledEq] using hcompiled


theorem localisedExp_of_expGlobalVarsList_eq_nil {α : Type _} {expressions : List (Exp α)}
    (h : expGlobalVars.expGlobalVarsList expressions = []) :
    ∀ expression ∈ expressions, localisedExp expression := by
  induction expressions with
  | nil => simp
  | cons head tail ih =>
      simp only [expGlobalVars.expGlobalVarsList] at h
      obtain ⟨hhead, htail⟩ := List.append_eq_nil_iff.mp h
      intro expression hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simpa [localisedExp] using hhead
      · exact ih htail expression hmem

theorem globalCompileExpList_expGlobalVars [BEq String] (context : GlobalPassContext α)
    (expressions : List (Exp α)) :
    expGlobalVars.expGlobalVarsList (globalCompileExpList context expressions) = [] := by
  induction expressions with
  | nil => simp [globalCompileExpList, expGlobalVars.expGlobalVarsList]
  | cons expression expressions ih =>
      simp only [globalCompileExpList, expGlobalVars.expGlobalVarsList]
      rw [globalCompileExp_expGlobalVars, ih]
      simp

theorem localisedExps_globalCompileExpList [BEq String] (context : GlobalPassContext α)
    (arguments : List (Exp α)) :
    ∀ expression ∈ globalCompileExpList context arguments, localisedExp expression :=
  localisedExp_of_expGlobalVarsList_eq_nil
    (globalCompileExpList_expGlobalVars context arguments)

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem globalCompileProg_localised [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (program : Prog α) :
    localisedProg (globalCompileProg context program) := by
  apply globalCompileProg.induct context
    (motive := fun program => localisedProg (globalCompileProg context program))
  · intro name shape value body ih
    simp [globalCompileProg, localisedProg, globalCompileExp_localised, ih]
  · intro name value shape address hlookup
    simp [globalCompileProg, localisedProg, hlookup, globalCompileExp_expGlobalVars,
      globalCompileExp_localised, localisedExp, expGlobalVars, expGlobalVars.expGlobalVarsList]
  · intro name value hlookup
    simp [globalCompileProg, localisedProg, hlookup]
  · intro name value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro name operator arguments
    simp only [globalCompileProg, localisedProg]
    exact localisedExps_globalCompileExpList context arguments
  · intro address value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro address value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro address value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro first second ihFirst ihSecond
    simp [globalCompileProg, localisedProg, ihFirst, ihSecond]
  · intro condition thenBranch elseBranch ihThen ihElse
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised, ihThen, ihElse]
  · intro condition body ih
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised, ih]
  · intro function arguments
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, trivial⟩
  · intro function arguments
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, trivial⟩
  · intro function arguments exception handlerVar handler ih
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, ih⟩
  · intro function arguments name
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, trivial⟩
  · intro function arguments name exception handlerVar handler ih
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, ih⟩
  · intro function arguments name shape address hlookup
    simp only [globalCompileProg, localisedProg, hlookup]
    refine ⟨localisedExps_globalCompileExpList context arguments, ?_⟩
    simp [localisedProg, localisedExp, expGlobalVars, expGlobalVars.expGlobalVarsList]
  · intro function arguments name hlookup
    simp only [globalCompileProg, localisedProg, hlookup]
    exact ⟨localisedExps_globalCompileExpList context arguments, trivial⟩
  · intro function arguments name exception handlerVar handler shape address hlookup ih
    simp only [globalCompileProg, localisedProg, hlookup]
    repeat' apply And.intro
    all_goals first
      | exact globalShapeVal_localised context shape
      | exact localisedExps_globalCompileExpList context arguments
      | exact ih
      | simp [localisedExp, expGlobalVars, expGlobalVars.expGlobalVarsList]
  · intro function arguments name exception handlerVar handler hlookup ih
    simp only [globalCompileProg, localisedProg, hlookup]
    exact ⟨localisedExps_globalCompileExpList context arguments, ih⟩
  · intro name shape function arguments body ih
    simp only [globalCompileProg, localisedProg]
    exact ⟨localisedExps_globalCompileExpList context arguments, ih⟩
  · intro function configuration configurationLength array arrayLength
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro exception value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro size name address
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro size name address globalAddress hlookup
    simp [globalCompileProg, localisedProg, hlookup, globalCompileExp_expGlobalVars,
      globalCompileExp_localised, localisedExp, expGlobalVars,
      expGlobalVars.expGlobalVarsList]
  · intro size name address h
    simp [globalCompileProg, localisedProg]
  · intro size address value
    simp [globalCompileProg, localisedProg, globalCompileExp_expGlobalVars,
      globalCompileExp_localised]
  · intro program hdec hassignG hassignL hprim hstore hstore32 hstorebyte hseq hite hwhile
      hcall hdeccall hextcall hraise hreturn hshmemload hshmemstore
    cases program with
    | skip => simp [globalCompileProg, localisedProg]
    | dec name shape value body => exact (hdec name shape value body rfl).elim
    | assign kind name value =>
        cases kind with
        | «local» => exact (hassignL name value rfl).elim
        | «global» => exact (hassignG name value rfl).elim
    | primitive name operator arguments => exact (hprim name operator arguments rfl).elim
    | store address value => exact (hstore address value rfl).elim
    | store32 address value => exact (hstore32 address value rfl).elim
    | storeByte address value => exact (hstorebyte address value rfl).elim
    | seq first second => exact (hseq first second rfl).elim
    | ite condition thenBranch elseBranch =>
        exact (hite condition thenBranch elseBranch rfl).elim
    | «while» condition body => exact (hwhile condition body rfl).elim
    | «break» => simp [globalCompileProg, localisedProg]
    | «continue» => simp [globalCompileProg, localisedProg]
    | call info function arguments => exact (hcall info function arguments rfl).elim
    | decCall name shape function arguments body =>
        exact (hdeccall name shape function arguments body rfl).elim
    | extCall function configuration configurationLength array arrayLength =>
        exact (hextcall function configuration configurationLength array arrayLength rfl).elim
    | raise exception value => exact (hraise exception value rfl).elim
    | «return» value => exact (hreturn value rfl).elim
    | shMemLoad size kind name address =>
        exact (hshmemload size kind name address rfl).elim
    | shMemStore size address value => exact (hshmemstore size address value rfl).elim
    | tick => simp [globalCompileProg, localisedProg]
    | annot tag text => simp [globalCompileProg, localisedProg]

theorem mem_of_globalDeclsFilter {predicate : Decl α → Bool} {declaration : Decl α}
    {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (ih htail))
      · simp [hpred] at hmem
        exact List.mem_cons.mpr (Or.inr (ih hmem))

theorem globalCompileDecls_function_bodies_localised [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    ∀ declaration ∈ globalCompileDecls context declarations,
      (match declaration with
       | .function function => localisedProg function.body
       | _ => True) := by
  induction declarations with
  | nil => simp [globalCompileDecls]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecls, List.mem_cons]
          intro found hmem
          rcases hmem with rfl | hmem
          · exact globalCompileProg_localised context function.body
          · exact ih found hmem
      | decl shape name value =>
          simp only [globalCompileDecls]
          intro found hmem
          exact ih found hmem
      | exnDecl exception shape =>
          simp only [globalCompileDecls, List.mem_cons]
          intro found hmem
          rcases hmem with rfl | hmem
          · trivial
          · exact ih found hmem
      | name struct fields =>
          simp only [globalCompileDecls]
          intro found hmem
          exact ih found hmem

theorem globalCompileDecs_functions_localised [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    ∀ entry ∈ functions (globalCompileDecs context code).functions,
      localisedProg entry.2.2.1 := by
  intro entry hmem
  simp only [globalCompileDecs] at hmem
  obtain ⟨declaration, hdecl, hentry⟩ := mem_functions hmem
  have hmemCompiled : (.function declaration : Decl α) ∈
      globalCompileDecls (globalCollect context code) code :=
    mem_of_globalDeclsFilter hdecl
  have hlocalised := globalCompileDecls_function_bodies_localised
    (globalCollect context code) code (.function declaration) hmemCompiled
  rw [hentry]
  simpa using hlocalised

theorem globalCompileInitializers_localised [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    ∀ initializer ∈ globalCompileInitializers context declarations,
      localisedProg initializer := by
  induction declarations generalizing context with
  | nil => simp [globalCompileInitializers]
  | cons declaration declarations ih =>
      cases declaration with
      | decl shape name value =>
          simp only [globalCompileInitializers, List.mem_cons]
          intro initializer hmem
          rcases hmem with rfl | hmem
          · refine ⟨?_, globalCompileExp_localised context value⟩
            simp [localisedExp, expGlobalVars, expGlobalVars.expGlobalVarsList]
          · exact ih _ initializer hmem
      | function function => simpa [globalCompileInitializers] using ih context
      | exnDecl exception shape => simpa [globalCompileInitializers] using ih context
      | name struct fields => simpa [globalCompileInitializers] using ih context



theorem localisedExp_var_local (name : VarName) :
    localisedExp (.var .local name : Exp α) := by
  simp [localisedExp, expGlobalVars]

theorem globalCompileDecs_function_decls_localised [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    ∀ declaration ∈ (globalCompileDecs context code).functions,
      (match declaration with
       | .function function => localisedProg function.body
       | _ => True) := by
  intro declaration hmem
  simp only [globalCompileDecs] at hmem
  exact globalCompileDecls_function_bodies_localised (globalCollect context code)
    code declaration (mem_of_globalDeclsFilter hmem)

theorem globalCompileTopForStart_functions_localised [BEq String] [LawfulBEq String]
    [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α))
    (start : FunName) (compiled : List (Decl α))
    (hcompile : globalCompileTopForStart bytesInWord fromNat declarations start =
      some compiled) :
    ∀ entry ∈ functions compiled, localisedProg entry.2.2.1 := by
  unfold globalCompileTopForStart at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some found =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      intro entry hmem
      obtain ⟨declaration, hdecl, hentry⟩ := mem_functions hmem
      rcases List.mem_append.mp hdecl with hprefix | hfunctiondecls
      · rcases List.mem_append.mp hprefix with hexceptions | hnewmain
        · have hpred := mem_globalDeclsFilter (predicate := globalDeclIsException)
            hexceptions
          cases declaration <;> simp [globalDeclIsException] at hpred
        · cases List.mem_singleton.mp hnewmain
          rw [hentry]
          simp only [localisedProg]
          refine ⟨?_, ?_⟩
          · exact (nestedSeq_localised _).mpr
              (globalCompileInitializers_localised _ _)
          · refine ⟨?_, trivial⟩
            intro expression hexpression
            obtain ⟨parameter, _, hparameter⟩ := List.mem_map.mp hexpression
            rw [← hparameter]
            exact localisedExp_var_local parameter.1
      · rw [hentry]
        exact globalCompileDecs_function_decls_localised _ _ (.function declaration) hfunctiondecls

end Flapjack
