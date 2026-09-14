import Flapjack.PanValues

/-!
# Pancake `h_prog_cond`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:307-317`.

The guard is evaluated before the selected program is exposed as a program
event.  An invalid or non-word guard returns `Error`; a failed event response
uses the original source state, while a returned result preserves its
post-state unchanged.
-/

namespace Flapjack

inductive PanHProgCondOutcome where
  | normal
  | error
  deriving DecidableEq, Repr

inductive PanHProgCondResponse (α : Type u) (σ : Type v) where
  | failed
  | returned (outcome : PanHProgCondOutcome) (sourceState : σ)
  deriving Repr

inductive PanHProgCondTree (α : Type u) (σ : Type v) where
  | ret (outcome : PanHProgCondOutcome) (sourceState : σ)
  | vis (program : Prog α) (sourceState : σ)
      (k : PanHProgCondResponse α σ → PanHProgCondTree α σ)

def panHProgCond [BEq α] [OfNat α 0]
    (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α) (thenBranch elseBranch : Prog α) :
    PanHProgCondTree α σ :=
  match eval sourceState guard with
  | some (.word value) =>
      let selected := if value == 0 then elseBranch else thenBranch
      .vis selected sourceState (fun response =>
        match response with
        | .failed => .ret .error sourceState
        | .returned outcome returnedState => .ret outcome returnedState)
  | _ => .ret .error sourceState

@[simp] theorem panHProgCond_invalid [BEq α] [OfNat α 0]
    (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α)
    (thenBranch elseBranch : Prog α)
    (heval : eval sourceState guard = none) :
    panHProgCond eval sourceState guard thenBranch elseBranch =
      .ret .error sourceState := by
  simp [panHProgCond, heval]

theorem panHProgCond_word [BEq α] [OfNat α 0]
    (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α)
    (thenBranch elseBranch : Prog α) (value : α)
    (heval : eval sourceState guard = some (.word value)) :
    panHProgCond eval sourceState guard thenBranch elseBranch =
      .vis (if value == 0 then elseBranch else thenBranch) sourceState (fun response =>
        match response with
        | .failed => .ret .error sourceState
        | .returned outcome returnedState => .ret outcome returnedState) := by
  simp [panHProgCond, heval]

end Flapjack
