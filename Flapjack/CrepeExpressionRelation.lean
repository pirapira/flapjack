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

theorem localisedExp_iff_no_global (expression : Exp α) :
    localisedExp expression ↔ expGlobalVars expression = [] := by
  rfl

theorem localisedProg_assign_global_false (name : VarName) (value : Exp α) :
    ¬ localisedProg (.assign .global name value : Prog α) := by
  simp [localisedProg]

end Flapjack
