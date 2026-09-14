import Flapjack.CrepeSemantics

/-!
# Crepe `exit_loop`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:234-237`.

The source result is carried by the evaluator together with its current
state.  This boundary preserves that state and decrements only the labelled
`Break` and `Continue` results; every other result, including `NONE`, passes
through unchanged.
-/

namespace Flapjack

def crepExitLoop : Option (CrepControlResult α) → Option (CrepControlResult α)
  | none => none
  | some (.broke state label) => some (.broke state (label - 1))
  | some (.continued state label) => some (.continued state (label - 1))
  | some result => some result

@[simp] theorem crepExitLoop_none {α : Type u} :
    crepExitLoop (none : Option (CrepControlResult α)) = none := rfl

@[simp] theorem crepExitLoop_broke {α : Type u}
    (state : CrepState α) (label : Nat) :
    crepExitLoop (some (.broke state label)) = some (.broke state (label - 1)) := rfl

@[simp] theorem crepExitLoop_continued {α : Type u}
    (state : CrepState α) (label : Nat) :
    crepExitLoop (some (.continued state label)) =
      some (.continued state (label - 1)) := rfl

end Flapjack
