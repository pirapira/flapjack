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

end Flapjack
