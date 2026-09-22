import Flapjack.PanGlobals
import Flapjack.Parser.Localise

namespace Flapjack

/-! HOL's localisation predicates, retained independently of the deleted
simplified Pan-to-Crep simulation layer. -/

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

end Flapjack
