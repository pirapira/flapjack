import Flapjack.Language

/-!
# Pancake `h_prog_seq`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:240-254`.

The source sequence handler emits the first program event, emits the second
only when the first returns `NONE`, and uses the original source state for
either exceptional event response.  This standalone tree makes those
program-event transitions explicit while keeping the source result/state pair
visible at every boundary.
-/

namespace Flapjack

inductive PanHProgSeqOutcome where
  | normal
  | error
  deriving DecidableEq, Repr

inductive PanHProgSeqResponse (α : Type u) (σ : Type v) where
  | failed
  | returned (outcome : PanHProgSeqOutcome) (sourceState : σ)
  deriving Repr

inductive PanHProgSeqTree (α : Type u) (σ : Type v) where
  | ret (outcome : PanHProgSeqOutcome) (sourceState : σ)
  | vis (program : Prog α) (sourceState : σ)
      (k : PanHProgSeqResponse α σ → PanHProgSeqTree α σ)

def panHProgSeq (sourceState : σ) (first second : Prog α) :
    PanHProgSeqTree α σ :=
  .vis first sourceState (fun firstResponse =>
    match firstResponse with
    | .failed => .ret .error sourceState
    | .returned firstOutcome firstState =>
        match firstOutcome with
        | .error => .ret .error firstState
        | .normal =>
            .vis second firstState (fun secondResponse =>
              match secondResponse with
              | .failed => .ret .error sourceState
              | .returned secondOutcome secondState =>
                  .ret secondOutcome secondState))

theorem panHProgSeq_first_normal (sourceState : σ)
    (first second : Prog α) :
    (panHProgSeq sourceState first second) =
      .vis first sourceState (fun firstResponse =>
        match firstResponse with
        | .failed => .ret .error sourceState
        | .returned firstOutcome returnedState =>
            match firstOutcome with
            | .error => .ret .error returnedState
            | .normal =>
                .vis second returnedState (fun secondResponse =>
                  match secondResponse with
                  | .failed => .ret .error sourceState
                  | .returned secondOutcome secondState =>
                      .ret secondOutcome secondState)) := by
  rfl

end Flapjack
