import Flapjack.Pancake.PanLang
import Flapjack.HolRef

/-!
# Pancake wordLang word operations

The word-level operation evaluator is shared by Pancake's word and Crepe
semantics. Keep its list behavior beside the Lean Pancake syntax rather than
inside a target backend.
-/

namespace Flapjack

/-! Flapjack's generic implementation helper for CakeML `word_op_def`.
This helper is deliberately untagged because HOL's declaration is over
fixed-width word types, not arbitrary Lean types carrying operation classes. -/
def wordOp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 0] (operator : BinOp) (values : List α) : Option α :=
  match operator, values with
  | .and, values =>
      some (values.foldr (fun left right => AndOp.and left right)
        (Complement.complement (0 : α)))
  | .add, values => some (values.foldr (fun left right => left + right) 0)
  | .or, values => some (values.foldr (fun left right => OrOp.or left right) 0)
  | .xor, values => some (values.foldr (fun left right => HXor.hXor left right) 0)
  | .sub, [left, right] => some (left - right)
  | _, _ => none

/-! Exact source counterpart of CakeML `wordLang$word_op_def`
(`cakeml/compiler/backend/wordLangScript.sml:302-311`). HOL quantifies over
`'a word`; Lean represents that polymorphic word width by `BitVec width`. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "word_op_def"]
def wordOpHOL [NeZero width] (operator : BinOp)
    (values : List (BitVec width)) : Option (BitVec width) :=
  wordOp operator values

end Flapjack
