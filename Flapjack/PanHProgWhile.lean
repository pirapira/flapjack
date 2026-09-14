import Flapjack.PanValues

/-!
# Pancake `h_prog_while`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:318-336`.

`h_prog_while` is defined through the potentially nonterminating HOL
`itree_iter`.  `panHProgWhileFuel` is its finite executable observation: each
fuel unit permits one guard/body transition, and exhaustion returns `none`
rather than inventing a terminal result.  The body response preserves the
source rules: `Break` exits normally, `Continue` and `NONE` re-enter the
loop, failed events use the state captured at the event, and other results
are retained as an opaque pass-through outcome.
-/

namespace Flapjack

inductive PanHProgWhileOutcome where
  | normal
  | error
  | break
  | continue
  | other
  deriving DecidableEq, Repr

inductive PanHProgWhileResponse (α : Type u) (σ : Type v) where
  | failed
  | returned (outcome : PanHProgWhileOutcome) (sourceState : σ)
  deriving Repr

inductive PanHProgWhileTree (α : Type u) (σ : Type v) where
  | ret (outcome : PanHProgWhileOutcome) (sourceState : σ)
  | tau (next : PanHProgWhileTree α σ)
  | vis (program : Prog α) (sourceState : σ)
      (k : PanHProgWhileResponse α σ → Option (PanHProgWhileTree α σ))

def panHProgWhileFuel [BEq α] [OfNat α 0]
    (fuel : Nat) (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α) (body : Prog α) :
    Option (PanHProgWhileTree α σ) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match eval sourceState guard with
      | some (.word value) =>
          if value == 0 then
            some (.ret .normal sourceState)
          else
            some (.vis body sourceState (fun response =>
              match response with
              | .failed => some (.ret .error sourceState)
              | .returned outcome bodyState =>
                  match outcome with
                  | .break => some (.ret .normal bodyState)
                  | .continue | .normal =>
                      (panHProgWhileFuel fuel eval bodyState guard body).map .tau
                  | .error => some (.ret .error bodyState)
                  | .other => some (.ret .other bodyState)))
      | _ => some (.ret .error sourceState)

@[simp] theorem panHProgWhileFuel_zero [BEq α] [OfNat α 0]
    (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α) (body : Prog α) :
    panHProgWhileFuel 0 eval sourceState guard body = none := by
  rfl

theorem panHProgWhileFuel_guard_invalid [BEq α] [OfNat α 0]
    (fuel : Nat) (eval : σ → Exp α → Option (PanValue α))
    (sourceState : σ) (guard : Exp α) (body : Prog α)
    (heval : eval sourceState guard = none) :
    panHProgWhileFuel (fuel + 1) eval sourceState guard body =
      some (.ret .error sourceState) := by
  simp [panHProgWhileFuel, heval]

end Flapjack
