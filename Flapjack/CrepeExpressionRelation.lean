import Flapjack.CrepeStateRelation
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

theorem localisedExp_iff_no_global (expression : Exp α) :
    localisedExp expression ↔ expGlobalVars expression = [] := by
  rfl

theorem localisedProg_assign_global_false (name : VarName) (value : Exp α) :
    ¬ localisedProg (.assign .global name value : Prog α) := by
  simp [localisedProg]

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

end Flapjack
